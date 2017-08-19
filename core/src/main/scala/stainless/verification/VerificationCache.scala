/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification


import java.io.ObjectInputStream
import java.io.FileInputStream
import java.io.ObjectOutputStream
import java.io.FileOutputStream

import inox.solvers.SolverFactory

object DebugSectionCache extends inox.DebugSection("vccache")
object DebugSectionCacheMiss extends inox.DebugSection("cachemiss")

class AppendingObjectOutputStream(os: java.io.OutputStream) extends ObjectOutputStream(os) {

  override protected def writeStreamHeader() = {
    // do not write a header, but reset:
    // this line added after another question
    // showed a problem with the original
    reset()
  }

}

trait VerificationCache extends VerificationChecker { self =>

  import program._
  import program.symbols._
  import program.trees._

  type SubProgram = inox.Program { val trees: program.trees.type }

  val uniq = new PrinterOptions(printUniqueIds = true)

  def buildDependencies(vc: VC): SubProgram = {

    var adts = Set[ADTDefinition]()
    var fundefs = Set[FunDef]()
    var traversed = Set[Identifier]()

    val traverser = new TreeTraverser {
      override def traverse(id: Identifier): Unit = {
        if (!traversed.contains(id)) {
          traversed += id
          if (program.symbols.functions.contains(id)) {
            val fd = program.symbols.functions(id)
            fundefs += fd
            traverse(fd)
          }
          else if (program.symbols.adts.contains(id)) {
            val adtdef = program.symbols.adts(id)
            adts += adtdef
            traverse(adtdef)
          }
        }
      }
    }

    traverser.traverse(vc.condition)

    new inox.Program {
      val trees: program.trees.type = program.trees
      val symbols = NoSymbols.withFunctions(fundefs.toSeq).withADTs(adts.toSeq)
      val ctx = program.ctx
    }
  }

  override def checkVC(vc: VC, sf: SolverFactory { val program: self.program.type }) = {
    import VerificationCache._

    inox.Bench.time("checking VC with cache", {
      ctx.reporter.debug("BUILDING DEPENDENCIES")(DebugSectionCache)
      val sp: SubProgram = inox.Bench.time("building dependencies", buildDependencies(vc))
      ctx.reporter.synchronized {
        ctx.reporter.debug(sp.symbols.asString(uniq))(DebugSectionCache)
        ctx.reporter.debug(vc.condition.asString(uniq))(DebugSectionCache)
      }
      val canonic = inox.Bench.time("canonizing", transformers.Canonization.canonize(sp.trees)(sp, vc))
      if (VerificationCache.contains(sp.trees)(canonic)) {
        ctx.reporter.synchronized {
          ctx.reporter.debug("The following VC has already been verified:")(DebugSectionCache)
          ctx.reporter.debug(vc.condition)(DebugSectionCache)
          ctx.reporter.debug("--------------")(DebugSectionCache)
        }
        VCResult(VCStatus.Valid, None, Some(0))
      }
      else {
        ctx.reporter.synchronized {
          ctx.reporter.debug("Cache miss:")(DebugSectionCacheMiss)
          ctx.reporter.debug(serialize(sp.trees)(canonic))(DebugSectionCacheMiss)
          ctx.reporter.debug("--------------")(DebugSectionCacheMiss)
        }
        val result = inox.Bench.time("checking VC from scratch", super.checkVC(vc,sf))
        VerificationCache.add(sp.trees)(canonic)
        VerificationCache.addVCToPersistentCache(sp.trees)(canonic, vc.toString, ctx)
        result
      }
    })
  }

}

object VerificationCache {
  val cacheFile = "vccache.bin"
  var vccache = scala.collection.concurrent.TrieMap[String,Unit]()
  println("loading persistent cache")
  inox.Bench.time("loading persistent cache", VerificationCache.loadPersistentCache())
    
  def contains(tt: inox.ast.Trees)(p: (tt.Symbols, tt.Expr)) = {
    inox.Bench.time("looking up VC in cache Map",
      vccache.contains(serialize(tt)(p))
    )
  }
    
  def add(tt: inox.ast.Trees)(p: (tt.Symbols, tt.Expr)) = {
    inox.Bench.time("adding VC to cache Map",
      vccache += ((serialize(tt)(p), ()))
    )
  }

  def serialize(tt: inox.ast.Trees)(p: (tt. Symbols, tt. Expr)): String = {
    val uniq = new tt.PrinterOptions(printUniqueIds = true)
    inox.Bench.time("transforming program to String", 
      p._1.asString(uniq) + "\n#\n" + p._2.asString(uniq)
    )
  }

  def addVCToPersistentCache(tt: inox.ast.Trees)(p: (tt. Symbols, tt. Expr), descr: String, ctx: inox.Context): Unit = {

    val task = new java.util.concurrent.Callable[String] {
      override def call(): String = {
        inox.Bench.time("adding VC to persistent cache", 
          MainHelpers.synchronized {
            val oos = 
              if (new java.io.File(cacheFile).exists) {
                ctx.reporter.debug("Opening already existing cache file.")(DebugSectionCache)
                new AppendingObjectOutputStream(new FileOutputStream(cacheFile, true))
              } else {
                ctx.reporter.debug("Creating new cache file")(DebugSectionCache)
                new ObjectOutputStream(new FileOutputStream(cacheFile))
              }
            oos.writeObject(serialize(tt)(p))
            descr
          }
        )
      }
    }
    MainHelpers.executor.submit(task)
  }
  
  def loadPersistentCache(): Unit = {
    if (new java.io.File(cacheFile).exists) {
      inox.Bench.time("loading persistent cache", {
        MainHelpers.synchronized {
          val ois = new ObjectInputStream(new FileInputStream(cacheFile))
          try {
            while (true) {
              val s = ois.readObject.asInstanceOf[String]
              // println("VERIFIED VC\n" + s + "\n---")
              vccache += ((s, ()))
            }
          } catch {
            case e: java.net.SocketTimeoutException => 
              // ctx.reporter.debug("Time out while reading cache")(DebugSectionCache)
            case e: java.io.EOFException =>
              // println("FINISHED READING CACHE")
              // ctx.reporter.debug("Reached end of cache file")(DebugSectionCache)
              ois.close()
            case e: java.io.IOException =>
              // ctx.reporter.debug("IO Error while reading cache")(DebugSectionCache)
              e.printStackTrace()
            case e: Throwable =>
              // ctx.reporter.debug("Error while reading cache")(DebugSectionCache)
              e.printStackTrace()
          }
        }
      })
    }
  }

}