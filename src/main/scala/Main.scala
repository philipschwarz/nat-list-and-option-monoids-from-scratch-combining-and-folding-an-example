
import Nat.*
import Option.{Some,None,some,none}
import List.*
import Semigroup.*

import scala.annotation.targetName

////////////////////////////////////////////////////////////////////////////

enum Nat:
  case Zero
  case Succ(n: Nat)

extension (m: Nat)

  def +(n: Nat): Nat = n match
    case Zero => m
    case Succ(n) => Succ(m + n)

  def *(n: Nat): Nat = n match
    case Zero => Zero
    case Succ(n) => m * n + m

////////////////////////////////////////////////////////////////////////////

sealed trait Semigroup[A]:
  def combine(x: A, y: A): A

object Semigroup:

  extension [A](lhs: A)(using m: Semigroup[A])
    def |+|(rhs: A): A = m.combine(lhs,rhs)

sealed trait Monoid[A] extends Semigroup[A]:
  def unit: A

////////////////////////////////////////////////////////////////////////////

enum List[+A]:
  case Cons(head: A, tail: List[A])
  case Nil

object List:

  def apply[A](as: A*): List[A] = as match
    case Seq() => Nil
    case _ => Cons(as.head,apply(as.tail*))

  def nil[A]: List[A] = Nil

  def append[A](lhs: List[A], rhs: List[A]): List[A] = lhs match
    case Nil => rhs
    case Cons(a, rest) => Cons(a,append(rest,rhs))

  extension [A](lhs: List[A])
    def ++(rhs: List[A]): List[A] = append(lhs,rhs)

  def fold[A](as: List[A])(using ma: Monoid[A]): A = as match
    case Nil => ma.unit
    case Cons(a,rest) => ma.combine(a,fold(rest))

////////////////////////////////////////////////////////////////////////////

enum Option[+A]:
  case None
  case Some(value:A)

object Option:

  def none[A]: Option[A] = None

  def some[A](a:A): Option[A] = Some(a)

  def fold[A](oa: Option[A])(using m: Monoid[A]): A = oa match
    case None => m.unit
    case Some(a) => a

////////////////////////////////////////////////////////////////////////////

given Monoid[Nat] with
  def unit: Nat = Zero
  def combine(x: Nat, y: Nat): Nat = x + y

val natMultMonoid : Monoid[Nat] = new Monoid[Nat]:
  def unit: Nat = Succ(Zero)
  def combine(x: Nat, y: Nat): Nat = x * y

given ListMonoid[A]: Monoid[List[A]] with
  def unit: List[A] = Nil
  def combine(lhs: List[A], rhs: List[A]): List[A] = lhs ++ rhs

given OptionMonoid[M](using m: Monoid[M]): Monoid[Option[M]] with
  def unit: Option[M] = None
  def combine(ox: Option[M], oy: Option[M]): Option[M] = (ox,oy) match
    case (None,_) => oy
    case (_, None) => ox
    case (Some(x),Some(y)) => Some(x |+| y)

@main def main: Unit =

  val zero = Zero
  val one = Succ(zero)
  val two = Succ(one)

  val three = Succ(two)
  val four = Succ(three)
  val five = Succ(four)
  val six = Succ(five)

  assert(zero + one == one)
  assert(one + zero == one)

  assert(one + two == three)
  assert(one + two + three == six)

  val ten = one + two + three + four

  assert(two * three == six)

  assert( (two |+| three) == five)

  val numbers: List[Nat] =
    Cons(one, Cons(two, Nil))

  val moreNumbers: List[Nat] = List(three, four)

  val allNumbers: List[Nat] = Cons(one, Cons(two, Cons(three, Cons(four, Nil))))

  assert(List(one,two,three) == Cons(one, Cons(two, Cons(three, Nil))))

  val yetMoreNumbers: List[Nat] = List(five,six)

  // use List[A]'s ++ function
  assert(numbers ++ moreNumbers == allNumbers)
  // use List monoid's combine function
  assert(summon[Monoid[List[Nat]]].combine(numbers,moreNumbers) == allNumbers)
  // use List monoid's infix combine operator
  assert((numbers |+| moreNumbers) == allNumbers)

  // fold List[Nat] with (+,0)
  assert(fold(allNumbers) == one + two + three + four)
  assert(fold(nil[Nat]) == Zero)
  // fold List[Nat] with (*,1)
  assert(fold(allNumbers)(using natMultMonoid) == one * two * three * four)
  assert(fold(Nil:List[Nat])(using natMultMonoid) == one)
  // fold List[List[Nat] with (List,combine)
  assert(fold(List(numbers,moreNumbers,yetMoreNumbers)) == List(one,two,three,four,five,six))

  // use Option monoid's combine function
  assert(summon[Monoid[Option[Nat]]].combine(Some(two),None) == Some(two))
  // use Option monoid's infix combine operator
  assert((some(two) |+| None) == Some(two))
  assert((none[Nat] |+| Some(two)) == Some(two))
  assert((some(two) |+| Some(three)) == Some(five))
  assert((none[Nat] |+| None) == None)
  assert(Option.fold(none[Nat] |+| None) == zero)

  val optionalNumbers: List[Option[Nat]] = List(Some(two),None,Some(three))

  val moreOptionalNumbers: List[Option[Nat]] = List(Some(one),None,Some(four))

  val allOptionalNumbers: List[Option[Nat]] = List(Some(two),None,Some(three),Some(one),None,Some(four))

  val yetMoreOptionalNumbers: List[Option[Nat]] = List(Some(five),None,Some(six))

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
  assert((some(List(one,two)) |+| None |+| Some(List(three,four))) == Some(List(one,two,three,four)))
  assert(Option.fold(some(List(one,two)) |+| None |+| Some(List(three,four))) == List(one,two,three,four))