
import Nat.*
import Option.*
import List.*

import scala.annotation.targetName

////////////////////////////////////////////////////////////////////////////

enum Nat:
  case Zero
  case Succ(n: Nat)

extension (m: Nat)
  @targetName("plus")
  def +(n: Nat): Nat = n match
    case Zero => m
    case Succ(n) => Succ(m + n)
  @targetName("times")
  def *(n: Nat): Nat = n match
    case Zero => Zero
    case Succ(n) => m * n + m

////////////////////////////////////////////////////////////////////////////

enum List[+A]:
  case Cons(head: A, tail: List[A])
  case Nil

object List:
  def apply[A](as: A*): List[A] = as match
    case Seq() => Nil
    case _ => Cons(as.head,apply(as.tail*))

def append[A](lhs: List[A], rhs: List[A]): List[A] = lhs match
  case Nil => rhs
  case Cons(a, rest) => Cons(a,append(rest,rhs))

extension [A](lhs: List[A])
  @targetName("plusplus")
  def ++(rhs: List[A]): List[A] = append(lhs,rhs)

////////////////////////////////////////////////////////////////////////////

enum Option[+A]:
  case None
  case Some(value:A)

////////////////////////////////////////////////////////////////////////////

sealed trait Semigroup[A]:
  def combine(x: A, y: A): A

sealed trait Monoid[A] extends Semigroup[A]:
  def unit: A

extension [A](lhs: A)(using m: Monoid[A])
  @targetName("monoidtiefighter")
  def |+|(rhs: A): A = m.combine(lhs,rhs)

given Monoid[Nat] with
  def unit: Nat = Zero
  def combine(x: Nat, y: Nat): Nat = x + y

val natMultMonoid : Monoid[Nat] = new Monoid[Nat]:
  def unit: Nat = Succ(Zero)
  def combine(x: Nat, y: Nat): Nat = x * y

given ListMonoid[A]: Monoid[List[A]] with
  def unit: List[A] = Nil
  def combine(lhs: List[A], rhs: List[A]): List[A] = lhs ++ rhs

def fold[A](as: List[A])(using ma: Monoid[A]): A = as match
  case Nil => ma.unit
  case Cons(a,rest) => ma.combine(a,fold(rest))

given OptionMonoid[M](using m: Monoid[M]): Monoid[Option[M]] with
  def unit: Option[M] = None
  def combine(ox: Option[M], oy: Option[M]): Option[M] = (ox,oy) match
    case (None,_) => oy
    case (_, None) => ox
    case (Some(x),Some(y)) => Some(x |+| y)

extension [A](lhs: Option[A])(using m: Monoid[Option[A]])
  @targetName("optionmonoidtiefighter")
  def |+|(rhs: Option[A]): Option[A] = m.combine(lhs,rhs)

@main def main: Unit =

  val unit = Zero
  val one = Succ(unit)
  val two = Succ(one)

  val three = Succ(two)
  val four = Succ(three)
  val five = Succ(four)
  val six = Succ(five)

  assert(unit + one == one)
  assert(one + unit == one)

  assert(one + two == three)
  assert(one + two + three == six)

  val ten = one + two + three + four

  assert(two * three == six)

  assert( (two |+| three) == five)

  val numbers: List[Nat] =
    Cons(one, Cons(two, Nil))

  val moreNumbers: List[Nat] = List(three, four)
    //    Cons(three, Cons(four, Nil))

  val allNumbers: List[Nat] = Cons(one, Cons(two, Cons(three, Cons(four, Nil))))

  // use List[A]'s ++ function
  assert(numbers ++ moreNumbers == allNumbers)
  // use List monoid's combine function
  assert(summon[Monoid[List[Nat]]].combine(numbers,moreNumbers) == allNumbers)
  // use List monoid's infix combine operator
  assert((numbers |+| moreNumbers) == allNumbers)

  // fold List[Nat] with (+,0)
  assert(fold(allNumbers) == one + two + three + four)
  // fold List[Nat] with (*,1)
  assert(fold(allNumbers)(using natMultMonoid) == one * two * three * four)

  // use Option monoid's combine function
  assert(summon[Monoid[Option[Nat]]].combine(Some(two),None) == Some(two))
  // use Option monoid's infix combine operator
  assert((Some(two) |+| None) == Some(two))
  assert(((None:Option[Nat]) |+| Some(two)) == Some(two))
  assert((Some(two) |+| Some(three)) == Some(five))

  val optionalNumbers: List[Option[Nat]] = List(Some(two),None,Some(three))
//    Cons(Some(two),
//      Cons(None,
//        Cons(Some(three),
//          Nil)))

  val moreOptionalNumbers: List[Option[Nat]] = List(Some(one),None,Some(four))
//    Cons(Some(one),
//      Cons(None,
//        Cons(Some(four),
//          Nil)))

  val allOptionalNumbers: List[Option[Nat]] = List(Some(two),None,Some(three),Some(one),None,Some(four))
//    Cons(Some(two),
//      Cons(None,
//        Cons(Some(three),
//          Cons(Some(one),
//            Cons(None,
//              Cons(Some(four),
//                Nil))))))

  val yetMoreOptionalNumbers: List[Option[Nat]] = List(Some(five),None,Some(six))
//    Cons(Some(five),
//      Cons(None,
//        Cons(Some(six),
//          Nil)))

  // fold List of Option[Nat] with (Option[Nat],combine)
  assert(fold(optionalNumbers) == Some(five))
  assert(fold(Cons(Some(two), Cons(None, Cons(Some(three), Nil)))) == Some(five))
  assert(fold(List(Some(two),None,Some(three))) == Some(five))

  // combine two lists of optional numbers
  assert((optionalNumbers ++ moreOptionalNumbers) == allOptionalNumbers)
  // use List[Option[Nat]] monoid's combine function
  assert(summon[Monoid[List[Option[Nat]]]].combine(optionalNumbers,moreOptionalNumbers) == allOptionalNumbers)
  // use List[Option[Nat]] monoid's infix combine operator
  assert((optionalNumbers |+| moreOptionalNumbers) == allOptionalNumbers)
  // fold the combination of two List[Option[Nat]] using (Option[Nat],combine)
  assert(fold(optionalNumbers |+| moreOptionalNumbers) == Some(ten))

  val listsOfOptionalNumbers = List(optionalNumbers,moreOptionalNumbers,yetMoreOptionalNumbers)
  //val listsOfOptionalNumbers = Cons(optionalNumbers,Cons(moreOptionalNumbers,Cons(yetMoreOptionalNumbers,Nil)))

  val twentyOne = five + five + five + six

  // fold the list of List[Option[Nat]] into a List[Option[Nat]] and then fold the latter using (Option[Nat],combine)
  assert(fold(fold(listsOfOptionalNumbers)) == Some(twentyOne))

  // combine three Option[List[Nat]] into a single Option[List[Nat]] by combining the lists using (List,combines)
  assert((Some(List(one,two)) |+| None |+| Some(List(three,four))) == Some(List(one,two,three,four)))