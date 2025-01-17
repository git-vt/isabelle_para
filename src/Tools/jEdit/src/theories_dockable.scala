/*  Title:      Tools/jEdit/src/theories_dockable.scala
    Author:     Makarius

Dockable window for theories managed by prover.
*/

package isabelle.jedit


import isabelle._
import isabelle.jedit_base.Dockable

import scala.swing.{Button, TextArea, Label, ListView, Alignment,
  ScrollPane, Component, CheckBox, BorderPanel}
import scala.swing.event.{ButtonClicked, MouseClicked, MouseMoved}

import java.awt.{BorderLayout, Graphics2D, Color, Point, Dimension}
import javax.swing.{JList, BorderFactory, UIManager}
import javax.swing.border.{BevelBorder, SoftBevelBorder}

import org.gjt.sp.jedit.{View, jEdit}


class Theories_Dockable(view: View, position: String) extends Dockable(view, position)
{
  /* status */

  private val status = new ListView(Nil: List[Document.Node.Name]) {
    background =
    {
      // enforce default value
      val c = UIManager.getDefaults.getColor("Panel.background")
      new Color(c.getRed, c.getGreen, c.getBlue, c.getAlpha)
    }
    listenTo(mouse.clicks)
    listenTo(mouse.moves)
    reactions += {
      case MouseClicked(_, point, _, clicks, _) =>
        val index = peer.locationToIndex(point)
        if (index >= 0) {
          if (in_checkbox(peer.indexToLocation(index), point)) {
            if (clicks == 1) Document_Model.node_required(listData(index), toggle = true)
          }
          else if (clicks == 2) PIDE.editor.goto_file(true, view, listData(index).node)
        }
      case MouseMoved(_, point, _) =>
        val index = peer.locationToIndex(point)
        val index_location = peer.indexToLocation(index)
        if (index >= 0 && in_checkbox(index_location, point))
          tooltip = "Mark as required for continuous checking"
        else if (index >= 0 && in_label(index_location, point)) {
          val name = listData(index)
          val st = overall_node_status(name)
          tooltip =
            "theory " + quote(name.theory) +
              (if (st == Overall_Node_Status.ok) "" else " (" + st + ")")
        }
        else tooltip = null
    }
  }
  status.peer.setLayoutOrientation(JList.HORIZONTAL_WRAP)
  status.peer.setVisibleRowCount(0)
  status.selection.intervalMode = ListView.IntervalMode.Single

  set_content(new ScrollPane(status))


  /* controls */

  def phase_text(phase: Session.Phase): String = "Prover: " + phase.print

  private val session_phase = new Label(phase_text(PIDE.session.phase))
  session_phase.border = new SoftBevelBorder(BevelBorder.LOWERED)
  session_phase.tooltip = "Status of prover session"

  private def handle_phase(phase: Session.Phase)
  {
    GUI_Thread.require {}
    session_phase.text = " " + phase_text(phase) + " "
  }

  private val purge = new Button("Purge") {
    tooltip = "Restrict document model to theories required for open editor buffers"
    reactions += { case ButtonClicked(_) => PIDE.editor.purge() }
  }

  private val continuous_checking = new Isabelle.Continuous_Checking
  continuous_checking.focusable = false

  private val logic = JEdit_Sessions.logic_selector(PIDE.options, true)

  private val controls =
    Wrap_Panel(List(purge, continuous_checking, session_phase, logic))

  add(controls.peer, BorderLayout.NORTH)


  /* component state -- owned by GUI thread */

  private var nodes_status: Map[Document.Node.Name, Protocol.Node_Status] = Map.empty
  private var nodes_required: Set[Document.Node.Name] = Document_Model.required_nodes()

  private object Overall_Node_Status extends Enumeration
  {
    val ok, failed, pending = Value
  }

  private def overall_node_status(name: Document.Node.Name): Overall_Node_Status.Value =
    nodes_status.get(name) match {
      case Some(st) if st.consolidated =>
        if (st.ok) Overall_Node_Status.ok else Overall_Node_Status.failed
      case _ => Overall_Node_Status.pending
    }

  private def in(geometry: Option[(Point, Dimension)], loc0: Point, p: Point): Boolean =
    geometry match {
      case Some((loc, size)) =>
        loc0.x + loc.x <= p.x && p.x < loc0.x + size.width &&
        loc0.y + loc.y <= p.y && p.y < loc0.y + size.height
      case None => false
    }

  private def in_checkbox(loc0: Point, p: Point): Boolean =
    Node_Renderer_Component != null && in(Node_Renderer_Component.checkbox_geometry, loc0, p)

  private def in_label(loc0: Point, p: Point): Boolean =
    Node_Renderer_Component != null && in(Node_Renderer_Component.label_geometry, loc0, p)


  private object Node_Renderer_Component extends BorderPanel
  {
    opaque = true
    border = BorderFactory.createEmptyBorder(2, 2, 2, 2)

    var node_name = Document.Node.Name.empty

    var checkbox_geometry: Option[(Point, Dimension)] = None
    val checkbox = new CheckBox {
      opaque = false
      override def paintComponent(gfx: Graphics2D)
      {
        super.paintComponent(gfx)
        if (location != null && size != null)
          checkbox_geometry = Some((location, size))
      }
    }

    var label_geometry: Option[(Point, Dimension)] = None
    val label = new Label {
      background = view.getTextArea.getPainter.getBackground
      foreground = view.getTextArea.getPainter.getForeground
      opaque = false
      xAlignment = Alignment.Leading

      override def paintComponent(gfx: Graphics2D)
      {
        def paint_segment(x: Int, w: Int, color: Color)
        {
          gfx.setColor(color)
          gfx.fillRect(x, 0, w, size.height)
        }

        paint_segment(0, size.width, background)
        nodes_status.get(node_name) match {
          case Some(st) if st.total > 0 =>
            val segments =
              List(
                (st.unprocessed, PIDE.options.color_value("unprocessed1_color")),
                (st.running, PIDE.options.color_value("running_color")),
                (st.warned, PIDE.options.color_value("warning_color")),
                (st.failed, PIDE.options.color_value("error_color"))
              ).filter(_._1 > 0)

            ((size.width - 2) /: segments)({ case (last, (n, color)) =>
              val w = (n * ((size.width - 4) - segments.length) / st.total) max 4
              paint_segment(last - w, w, color)
              last - w - 1
            })

          case _ =>
            paint_segment(0, size.width, PIDE.options.color_value("unprocessed1_color"))
        }
        super.paintComponent(gfx)

        if (location != null && size != null)
          label_geometry = Some((location, size))
      }
    }

    def label_border(name: Document.Node.Name)
    {
      val status = overall_node_status(name)
      val color =
        if (status == Overall_Node_Status.failed) PIDE.options.color_value("error_color")
        else label.foreground
      val thickness1 = if (status == Overall_Node_Status.pending) 1 else 2
      val thickness2 = 3 - thickness1

      label.border =
        BorderFactory.createCompoundBorder(
          BorderFactory.createLineBorder(color, thickness1),
          BorderFactory.createEmptyBorder(thickness2, thickness2, thickness2, thickness2))
    }

    layout(checkbox) = BorderPanel.Position.West
    layout(label) = BorderPanel.Position.Center
  }

  private class Node_Renderer extends ListView.Renderer[Document.Node.Name]
  {
    def componentFor(list: ListView[_ <: isabelle.Document.Node.Name], isSelected: Boolean,
      focused: Boolean, name: Document.Node.Name, index: Int): Component =
    {
      val component = Node_Renderer_Component
      component.node_name = name
      component.checkbox.selected = nodes_required.contains(name)
      component.label_border(name)
      component.label.text = name.theory_base_name
      component
    }
  }
  status.renderer = new Node_Renderer

  private def handle_update(restriction: Option[Set[Document.Node.Name]] = None)
  {
    GUI_Thread.require {}

    val snapshot = PIDE.session.snapshot()
    val nodes = snapshot.version.nodes

    val nodes_status1 =
      (nodes_status /: (restriction.getOrElse(nodes.domain).iterator))(
        { case (status, name) =>
            if (PIDE.resources.is_hidden(name) ||
                PIDE.resources.session_base.loaded_theory(name) ||
                nodes(name).is_empty) status
            else {
              val st = Protocol.node_status(snapshot.state, snapshot.version, name)
              status + (name -> st)
            }
        })

    val nodes_status2 =
      nodes_status1 -- nodes_status1.keysIterator.filter(nodes.is_suppressed(_))

    if (nodes_status != nodes_status2) {
      nodes_status = nodes_status2
      status.listData = nodes.topological_order.filter(nodes_status.isDefinedAt(_))
    }
  }


  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case phase: Session.Phase =>
        GUI_Thread.later { handle_phase(phase) }

      case _: Session.Global_Options =>
        GUI_Thread.later {
          continuous_checking.load()
          logic.load ()
          nodes_required = Document_Model.required_nodes()
          status.repaint()
        }

      case changed: Session.Commands_Changed =>
        GUI_Thread.later { handle_update(Some(changed.nodes)) }
    }

  override def init()
  {
    PIDE.session.phase_changed += main
    PIDE.session.global_options += main
    PIDE.session.commands_changed += main

    handle_phase(PIDE.session.phase)
    handle_update()
  }

  override def exit()
  {
    PIDE.session.phase_changed -= main
    PIDE.session.global_options -= main
    PIDE.session.commands_changed -= main
  }
}
