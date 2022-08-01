
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

trait Semigroup[A]:
  def combine(x: A, y: A): A

object Semigroup:

  extension [A](lhs: A)(using m: Semigroup[A])
    def ⨁(rhs: A): A = m.combine(lhs,rhs)

trait Monoid[A] extends Semigroup[A]:
  def unit: A

////////////////////////////////////////////////////////////////////////////

enum List[+A]:
  case Cons(head: A, tail: List[A])
  case Nil

object List:

  def apply[A](as: A*): List[A] = as match
    case Seq() => Nil
    case _ => Cons(as.head,List(as.tail*))

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

val natMultMonoid = new Monoid[Nat]:
  def unit: Nat = Succ(Zero)
  def combine(x: Nat, y: Nat): Nat = x * y

given ListMonoid[A]: Monoid[List[A]] with
  def unit: List[A] = Nil
  def combine(lhs: List[A], rhs: List[A]): List[A] = lhs ++ rhs

given OptionMonoid[M:Semigroup]: Monoid[Option[M]] with
  def unit: Option[M] = None
  def combine(ox: Option[M], oy: Option[M]): Option[M] = (ox,oy) match
    case (None,_) => oy
    case (_, None) => ox
    case (Some(x),Some(y)) => Some(x ⨁ y)

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

  assert(two * one == two)
  assert(one * two == two)
  assert(two * three == six)

  assert( summon[Monoid[Nat]].combine(two,three) == five)
  assert( (two ⨁ three) == five)
  assert( (one ⨁ two ⨁ three) == six)

  val oneTwo = Cons(one, Cons(two, Nil))
  val threeFour = Cons(three, Cons(four, Nil))

  assert(append(oneTwo,threeFour) == Cons(one, Cons(two, Cons(three, Cons(four, Nil)))))
  assert(oneTwo ++ threeFour == Cons(one, Cons(two, Cons(three, Cons(four, Nil)))))

  assert(List(one,two,three) == Cons(one, Cons(two, Cons(three, Nil))))

  val numbers: List[Nat] = List(one,two)

  val moreNumbers: List[Nat] = List(three, four)

  val allNumbers: List[Nat] = Cons(one, Cons(two, Cons(three, Cons(four, Nil))))

  val yetMoreNumbers: List[Nat] = List(five,six)

  // use List[A]'s ++ function
  assert(List(one,two) ++ List(three, four) == List(one,two,three,four))
  // use List monoid's combine function
  assert(summon[Monoid[List[Nat]]].combine(List(one,two),List(three, four)) == List(one,two,three,four))
  // use List monoid's infix combine operator
  assert((List(one,two) ⨁ List(three, four) ⨁ Nil) == List(one,two,three,four))

  // fold List[Nat] with (+,0)
  assert(fold(List(one,two,three,four)) == one + two + three + four)
  assert(fold(nil[Nat]) == Zero)
  // fold List[Nat] with (*,1)
  assert(fold(List(one,two,three,four))(using natMultMonoid) == one * two * three * four)
  assert(fold(nil[Nat])(using natMultMonoid) == one)
  // fold List[List[Nat] with (List,combine)
  assert(fold(List(List(one,two),Nil,List(three, four),List(five,six))) == List(one,two,three,four,five,six))

  // use Option monoid's combine function
  assert(summon[Monoid[Option[Nat]]].combine(Some(two),Some(three)) == Some(five))
  assert(summon[Monoid[Option[Nat]]].combine(Some(two),None) == Some(two))
  assert(summon[Monoid[Option[Nat]]].combine(none[Nat],Some(two)) == Some(two))
  assert(summon[Monoid[Option[Nat]]].combine(none[Nat],None) == None)
  // use Option monoid's infix combine operator
  assert((some(two) ⨁ None) == Some(two))
  assert((none[Nat] ⨁ Some(two)) == Some(two))
  assert((some(two) ⨁ Some(three)) == Some(five))
  assert((none[Nat] ⨁ None) == None)
  assert(Option.fold(none[Nat] ⨁ None) == zero)

  val allOptionalNumbers: List[Option[Nat]] = List(Some(two),None,Some(three),Some(one),None,Some(four))

  // fold List of Option[Nat] with (Option[Nat],combine)
  assert(fold(List(Some(two),None,Some(three))) == Some(five))
  assert(fold(nil[Option[Nat]]) == None)

  // combine two lists of optional numbers
  assert((List(Some(one),None,Some(three)) ++ List(Some(four),None,Some(six)))
          == List(Some(one),None,Some(three),Some(four),None,Some(six)))
  // use List[Option[Nat]] monoid's combine function
  assert(summon[Monoid[List[Option[Nat]]]].combine(List(Some(one),None,Some(two)),List(Some(three),None,Some(four)))
         == List(Some(one),None,Some(two),Some(three),None,Some(four)))
  // use List[Option[Nat]] monoid's infix combine operator
  assert((List(Some(one),None,Some(two)) ⨁ List(Some(three),None,Some(four)))
          == List(Some(one),None,Some(two),Some(three),None,Some(four)))
  // fold the combination of two List[Option[Nat]] using (Option[Nat],combine)
  assert(fold(List(Some(one),None,Some(two)) ⨁ List(Some(three),None,Some(four))) == Some(one + two + three + four))

  //val listsOfOptionalNumbers = Cons(optionalNumbers,Cons(moreOptionalNumbers,Cons(yetMoreOptionalNumbers,Nil)))

  val twentyOne = five + five + five + six

  // fold the list of List[Option[Nat]] into a List[Option[Nat]] and then fold the latter using (Option[Nat],combine)
  assert(
    fold(
      fold(
        List(List(Some(one), None, Some(two)),
             List(Some(three), None, Some(four)),
             List(Some(five), None, Some(six)))))
    == Some(one + two + three + four + five + six))

  // combine three Option[List[Nat]] into a single Option[List[Nat]] by combining the lists using (List,combines)
  assert((some(List(one,two)) ⨁ None ⨁ Some(List(three,four))) == Some(List(one,two,three,four)))
  assert(Option.fold(some(List(one,two)) ⨁ None ⨁ Some(List(three,four))) == List(one,two,three,four))