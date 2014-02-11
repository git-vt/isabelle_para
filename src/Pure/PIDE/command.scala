/*  Title:      Pure/PIDE/command.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Prover commands with accumulated results from execution.
*/

package isabelle


import scala.collection.mutable
import scala.collection.immutable.SortedMap


object Command
{
  type Edit = (Option[Command], Option[Command])


  /** accumulated results from prover **/

  /* results */

  object Results
  {
    type Entry = (Long, XML.Tree)
    val empty = new Results(SortedMap.empty)
    def make(es: Iterable[Results.Entry]): Results = (empty /: es.iterator)(_ + _)
    def merge(rs: Iterable[Results]): Results = (empty /: rs.iterator)(_ ++ _)
  }

  final class Results private(private val rep: SortedMap[Long, XML.Tree])
  {
    def defined(serial: Long): Boolean = rep.isDefinedAt(serial)
    def get(serial: Long): Option[XML.Tree] = rep.get(serial)
    def entries: Iterator[Results.Entry] = rep.iterator

    def + (entry: Results.Entry): Results =
      if (defined(entry._1)) this
      else new Results(rep + entry)

    def ++ (other: Results): Results =
      if (this eq other) this
      else if (rep.isEmpty) other
      else (this /: other.entries)(_ + _)

    override def hashCode: Int = rep.hashCode
    override def equals(that: Any): Boolean =
      that match {
        case other: Results => rep == other.rep
        case _ => false
      }
    override def toString: String = entries.mkString("Results(", ", ", ")")
  }


  /* state */

  sealed case class State(
    command: Command,
    status: List[Markup] = Nil,
    results: Results = Results.empty,
    markups: Map[String, Markup_Tree] = Map.empty)
  {
    def get_markup(file_name: String): Markup_Tree =
      markups.getOrElse(file_name, Markup_Tree.empty)

    def markup: Markup_Tree = get_markup("")

    def markup_to_XML(filter: XML.Elem => Boolean): XML.Body =
      markup.to_XML(command.range, command.source, filter)


    /* content */

    def eq_content(other: State): Boolean =
      command.source == other.command.source &&
      status == other.status &&
      results == other.results &&
      markup == other.markup

    private def add_status(st: Markup): State = copy(status = st :: status)

    private def add_markup(file_name: String, m: Text.Markup): State =
      copy(markups = markups + (file_name -> (get_markup(file_name) + m)))

    def + (alt_id: Document_ID.Generic, message: XML.Elem): State =
      message match {
        case XML.Elem(Markup(Markup.STATUS, _), msgs) =>
          (this /: msgs)((state, msg) =>
            msg match {
              case elem @ XML.Elem(markup, Nil) =>
                state.add_status(markup)
                  .add_markup("", Text.Info(command.proper_range, elem))  // FIXME cumulation order!?

              case _ =>
                java.lang.System.err.println("Ignored status message: " + msg)
                state
            })

        case XML.Elem(Markup(Markup.REPORT, _), msgs) =>
          (this /: msgs)((state, msg) =>
            {
              def bad(): Unit = java.lang.System.err.println("Ignored report message: " + msg)

              msg match {
                case XML.Elem(Markup(name, atts @ Position.Reported(id, file_name, raw_range)), args)
                if id == command.id || id == alt_id =>
                  command.chunks.get(file_name) match {
                    case Some(chunk) =>
                      val range = chunk.decode(raw_range)
                      if (chunk.range.contains(range)) {
                        val props = Position.purge(atts)
                        val info: Text.Markup = Text.Info(range, XML.Elem(Markup(name, props), args))
                        state.add_markup(file_name, info)
                      }
                      else {
                        bad()
                        state
                      }
                    case None =>
                      bad()
                      state
                  }

                case XML.Elem(Markup(name, atts), args)
                if !atts.exists({ case (a, _) => Markup.POSITION_PROPERTIES(a) }) =>
                  val range = command.proper_range
                  val props = Position.purge(atts)
                  val info: Text.Markup = Text.Info(range, XML.Elem(Markup(name, props), args))
                  state.add_markup("", info)

                case _ =>
                  // FIXME bad()
                  state
              }
            })
        case XML.Elem(Markup(name, props), body) =>
          props match {
            case Markup.Serial(i) =>
              val message1 = XML.Elem(Markup(Markup.message(name), props), body)
              val message2 = XML.Elem(Markup(name, props), body)

              val st0 = copy(results = results + (i -> message1))
              val st1 =
                if (Protocol.is_inlined(message)) {
                  var st1 = st0
                  for {
                    (file_name, chunk) <- command.chunks
                    range <- Protocol.message_positions(command.id, chunk, message)
                  } st1 = st1.add_markup(file_name, Text.Info(range, message2))
                  st1
                }
                else st0

              st1

            case _ =>
              java.lang.System.err.println("Ignored message without serial number: " + message)
              this
          }
      }

    def ++ (other: State): State =
      copy(
        status = other.status ::: status,
        results = results ++ other.results,
        markups =
          (markups.keySet ++ other.markups.keySet)
            .map(a => a -> (get_markup(a) ++ other.get_markup(a))).toMap
      )
  }



  /** static content **/

  /* text chunks */

  abstract class Chunk
  {
    def file_name: String
    def length: Int
    def range: Text.Range
    def decode(r: Text.Range): Text.Range
  }

  class File(val file_name: String, text: CharSequence) extends Chunk
  {
    val length = text.length
    val range = Text.Range(0, length)
    private val symbol_index = Symbol.Index(text)
    def decode(r: Text.Range): Text.Range = symbol_index.decode(r)
  }


  /* make commands */

  def name(span: List[Token]): String =
    span.find(_.is_command) match { case Some(tok) => tok.source case _ => "" }

  type Blob = Exn.Result[(Document.Node.Name, Option[(SHA1.Digest, File)])]

  def apply(
    id: Document_ID.Command,
    node_name: Document.Node.Name,
    blobs: List[Blob],
    span: List[Token],
    results: Results = Results.empty,
    markup: Markup_Tree = Markup_Tree.empty): Command =
  {
    val source: String =
      span match {
        case List(tok) => tok.source
        case _ => span.map(_.source).mkString
      }

    val span1 = new mutable.ListBuffer[Token]
    var i = 0
    for (Token(kind, s) <- span) {
      val n = s.length
      val s1 = source.substring(i, i + n)
      span1 += Token(kind, s1)
      i += n
    }

    new Command(id, node_name, blobs, span1.toList, source, results, markup)
  }

  val empty = Command(Document_ID.none, Document.Node.Name.empty, Nil, Nil)

  def unparsed(id: Document_ID.Command, source: String, results: Results, markup: Markup_Tree)
      : Command =
    Command(id, Document.Node.Name.empty, Nil, List(Token(Token.Kind.UNPARSED, source)),
      results, markup)

  def unparsed(source: String): Command =
    unparsed(Document_ID.none, source, Results.empty, Markup_Tree.empty)

  def rich_text(id: Document_ID.Command, results: Results, body: XML.Body): Command =
  {
    val text = XML.content(body)
    val markup = Markup_Tree.from_XML(body)
    unparsed(id, text, results, markup)
  }


  /* perspective */

  object Perspective
  {
    val empty: Perspective = Perspective(Nil)
  }

  sealed case class Perspective(commands: List[Command])  // visible commands in canonical order
  {
    def same(that: Perspective): Boolean =
    {
      val cmds1 = this.commands
      val cmds2 = that.commands
      require(!cmds1.exists(_.is_undefined))
      require(!cmds2.exists(_.is_undefined))
      cmds1.length == cmds2.length &&
        (cmds1.iterator zip cmds2.iterator).forall({ case (c1, c2) => c1.id == c2.id })
    }
  }
}


final class Command private(
    val id: Document_ID.Command,
    val node_name: Document.Node.Name,
    val blobs: List[Command.Blob],
    val span: List[Token],
    val source: String,
    val init_results: Command.Results,
    val init_markup: Markup_Tree)
  extends Command.Chunk
{
  /* classification */

  def is_undefined: Boolean = id == Document_ID.none
  val is_unparsed: Boolean = span.exists(_.is_unparsed)
  val is_unfinished: Boolean = span.exists(_.is_unfinished)

  val is_ignored: Boolean = !span.exists(_.is_proper)
  val is_malformed: Boolean = !is_ignored && (!span.head.is_command || span.exists(_.is_error))
  def is_command: Boolean = !is_ignored && !is_malformed

  def name: String = Command.name(span)

  override def toString =
    id + "/" + (if (is_command) name else if (is_ignored) "IGNORED" else "MALFORMED")


  /* blobs */

  def blobs_names: List[Document.Node.Name] =
    for (Exn.Res((name, _)) <- blobs) yield name

  def blobs_digests: List[SHA1.Digest] =
    for (Exn.Res((_, Some((digest, _)))) <- blobs) yield digest

  val chunks: Map[String, Command.Chunk] =
    (("" -> this) ::
      (for (Exn.Res((name, Some((_, file)))) <- blobs) yield (name.node -> file))).toMap


  /* source */

  def file_name: String = ""

  def length: Int = source.length
  val range: Text.Range = Text.Range(0, length)

  val proper_range: Text.Range =
    Text.Range(0, (length /: span.reverse.iterator.takeWhile(_.is_improper))(_ - _.source.length))

  def source(range: Text.Range): String = source.substring(range.start, range.stop)

  private lazy val symbol_index = Symbol.Index(source)
  def decode(i: Text.Offset): Text.Offset = symbol_index.decode(i)
  def decode(r: Text.Range): Text.Range = symbol_index.decode(r)


  /* accumulated results */

  val init_state: Command.State =
    Command.State(this, results = init_results, markups = Map("" -> init_markup))

  val empty_state: Command.State = Command.State(this)
}
