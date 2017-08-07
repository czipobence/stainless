/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification


import java.io.ObjectInputStream
import java.io.FileInputStream
import java.io.ObjectOutputStream
import java.io.FileOutputStream

import inox.solvers.SolverFactory

object DebugSectionCache extends inox.DebugSection("vccache")

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

    var adts = Set[(Identifier,ADTDefinition)]()
    var fundefs = Set[FunDef]()
    var traversedExpr = Set[Expr]()
    var traversedTypes = Set[Type]()

    val traverser = new TreeTraverser {
      override def traverse(e: Expr): Unit = {
        if (!traversedExpr.contains(e)) {
          traversedExpr += e
          val callees = inox.Bench.time("getting transitive callees", {
            exprOps.functionCallsOf(e).flatMap(fi => transitiveCallees(fi.tfd.fd) + fi.tfd.fd)
          })
          fundefs = fundefs ++ callees
          super.traverse(e)
        }
      }
      override def traverse(tpe: Type): Unit = {
        if (!traversedTypes.contains(tpe)) {
          traversedTypes += tpe
          tpe match {
            case adt: ADTType =>
              val id = adt.id
              val a = getADT(adt.id)
              a.invariant.map(inv => traverse(inv.fullBody))
              adts += ((id,a))
            case _ => ()
          }
          super.traverse(tpe)
        }
      }
    }

    traverser.traverse(vc.condition)

    new inox.Program {
      val trees: program.trees.type = program.trees
      val symbols = NoSymbols.withFunctions(fundefs.toSeq).withADTs(adts.map(_._2).toSeq)
      val ctx = program.ctx
    }
  }

  override def checkVC(vc: VC, sf: SolverFactory { val program: self.program.type }) = {
    import VerificationCache._

    val sp: SubProgram = inox.Bench.time("building dependencies", buildDependencies(vc))
    val canonic = transformers.Canonization.canonize(sp.trees)(sp, vc)
    if (VerificationCache.contains(sp.trees)(canonic)) {
      ctx.reporter.synchronized {
        ctx.reporter.debug("The following VC has already been verified:")(DebugSectionCache)
        ctx.reporter.debug(vc)(DebugSectionCache)
        ctx.reporter.debug("--------------")(DebugSectionCache)
      }
      VCResult(VCStatus.Valid, None, Some(0))
    }
    else {
      val result = inox.Bench.time("checking VC", super.checkVC(vc,sf))
      VerificationCache.add(sp.trees)(canonic)
      VerificationCache.addVCToPersistentCache(sp.trees)(canonic, vc.toString, ctx)
      result
    }
  }

}

object VerificationCache {
  val cacheFile = "vccache.bin"
  var vccache = scala.collection.concurrent.TrieMap[String,Unit]()
  inox.Bench.time("loading persistent cache", VerificationCache.loadPersistentCache())
    
  def contains(tt: inox.ast.Trees)(p: (tt.Symbols, tt.Expr)) = {
    vccache.contains(serialize(tt)(p))
  }
    
  def add(tt: inox.ast.Trees)(p: (tt.Symbols, tt.Expr)) = {
    vccache += ((serialize(tt)(p), ()))
  }

  def serialize(tt: inox.ast.Trees)(p: (tt. Symbols, tt. Expr)): String = {
    val uniq = new tt.PrinterOptions(printUniqueIds = true)
    inox.Bench.time("serializing", 
      p._1.asString(uniq) + "\n#\n" + p._2.asString(uniq)
    )
  }

  def addVCToPersistentCache(tt: inox.ast.Trees)(p: (tt. Symbols, tt. Expr), descr: String, ctx: inox.Context): Unit = {

    val task = new java.util.concurrent.Callable[String] {
      override def call(): String = {
        MainHelpers.synchronized {
          // println("WRITING VC")
          val oos = 
            if (new java.io.File(cacheFile).exists) {
              ctx.reporter.debug("Opening already existing cache file.")(DebugSectionCache)
              new AppendingObjectOutputStream(new FileOutputStream(cacheFile, true))
            } else {
              ctx.reporter.debug("Creating new cache file")(DebugSectionCache)
              new ObjectOutputStream(new FileOutputStream(cacheFile))
            }
          oos.writeObject(serialize(tt)(p))
          // println("FINISHED VC")
          descr
        }
      }
    }
    MainHelpers.executor.submit(task)
  }
  
  def loadPersistentCache(): Unit = {
    if (new java.io.File(cacheFile).exists) {
      MainHelpers.synchronized {
        // println("READING THE WHOLE CACHE")
        val ois = new ObjectInputStream(new FileInputStream(cacheFile))
        // println("OPENED THE OBJECT INPUT STREAM")
        try {
          // println("WHILING")
          while (true) {
            val s = ois.readObject.asInstanceOf[String]
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
        // println("SYNCHRONIZED END")
      }
    }
  }

}