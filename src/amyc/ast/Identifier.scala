package amyc.ast

object Identifier {
  private val counter = new amyc.utils.UniqueCounter[String]
  val ASSIGNABLE = true

  def fresh(name: String, assignable: Boolean): Identifier = new Identifier(name, assignable)
  def fresh(name: String): Identifier = new Identifier(name, !ASSIGNABLE)
}

// Denotes a unique identifier in an Amy program
// Notice that we rely on reference equality to compare Identifiers.
// The numeric id will be generated lazily,
// so the Identifiers are numbered in order when we print the program.
final class Identifier private(val name: String, val assignable: Boolean) {
  private lazy val id = Identifier.counter.next(name)
  def fullName = s"${name}_$id"

  override def toString: String = name
}
