/*  Title:      Pure/Tools/cygwin.scala
    Author:     Makarius

Cygwin as POSIX emulation on Windows.
*/

package isabelle


import java.io.{File => JFile}
import java.nio.file.Files

import scala.annotation.tailrec


object Cygwin
{
  /* init (e.g. after extraction via 7zip) */

  def init(isabelle_home: String, cygwin_root: String)
  {
    require(Platform.is_windows)

    def execute(args: String*)
    {
      val cwd = new JFile(isabelle_home)
      val env = Map("CYGWIN" -> "nodosfilewarning")
      val proc = Isabelle_System.raw_execute(cwd, env, true, args: _*)
      val (output, rc) = Isabelle_System.process_output(proc)
      if (rc != 0) error(output)
    }

    val uninitialized_file = new JFile(cygwin_root, "isabelle\\uninitialized")
    val uninitialized = uninitialized_file.isFile && uninitialized_file.delete

    if (uninitialized) {
      val symlinks =
      {
        val path = (new JFile(cygwin_root + "\\isabelle\\symlinks")).toPath
        Files.readAllLines(path, UTF8.charset).toArray.toList.asInstanceOf[List[String]]
      }
      @tailrec def recover_symlinks(list: List[String]): Unit =
      {
        list match {
          case Nil | List("") =>
          case link :: content :: rest =>
            val path = (new JFile(isabelle_home, link)).toPath

            val writer = Files.newBufferedWriter(path, UTF8.charset)
            try { writer.write("!<symlink>" + content + "\u0000") }
            finally { writer.close }

            Files.setAttribute(path, "dos:system", true)

            recover_symlinks(rest)
          case _ => error("Unbalanced symlinks list")
        }
      }
      recover_symlinks(symlinks)

      execute(cygwin_root + "\\bin\\dash.exe", "/isabelle/rebaseall")
      execute(cygwin_root + "\\bin\\bash.exe", "/isabelle/postinstall")
    }
  }
}
