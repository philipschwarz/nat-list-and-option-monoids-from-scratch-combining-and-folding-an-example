
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

  def foldRight[A,B](as: List[A], b: B, f: (A, B) => B): B = as match
    case Nil => b
    case Cons(a,rest) => f(a,foldRight(rest,b,f))

  def fold[A](as: List[A])(using ma: Monoid[A]): A =
    foldRight(as, ma.unit, (a,b) => ma.combine(a,b))

////////////////////////////////////////////////////////////////////////////

enum Option[+A]:
  case None
  case Some(value:A)

object Option:

  def none[A]: Option[A] = None

  def some[A](a:A): Option[A] = Some(a)

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

given OptionMonoid[A:Semigroup]: Monoid[Option[A]] with
  def unit: Option[A] = None
  def combine(ox: Option[A], oy: Option[A]): Option[A] = (ox,oy) match
    case (None,_) => oy
    case (_, None) => ox
    case (Some(x),Some(y)) => Some(x ⨁ y)

////////////////////////////////////////////////////////////////////////////

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

  assert(two * one == two)
  assert(one * two == two)
  assert(two * three == six)

  ////////////////////////////////////////////////////////////////////////////

  assert( summon[Monoid[Nat]].combine(two,three) == five)
  assert( (two ⨁ three) == five)
  assert( (one ⨁ two ⨁ three) == six)

  ////////////////////////////////////////////////////////////////////////////

  val oneTwo = Cons(one, Cons(two, Nil))
  val threeFour = Cons(three, Cons(four, Nil))

  assert(append(oneTwo,threeFour) == Cons(one, Cons(two, Cons(three, Cons(four, Nil)))))
  assert(oneTwo ++ threeFour == Cons(one, Cons(two, Cons(three, Cons(four, Nil)))))

  ////////////////////////////////////////////////////////////////////////////

  assert(List(one,two,three) == Cons(one, Cons(two, Cons(three, Nil))))
  assert(List(one,two) ++ List(three, four) == List(one,two,three,four))

  assert(summon[Monoid[List[Nat]]].combine(List(one,two),List(three, four)) == List(one,two,three,four))
  assert((List(one,two) ⨁ List(three, four) ⨁ Nil) == List(one,two,three,four))

  ////////////////////////////////////////////////////////////////////////////

  assert(fold(List(one,two,three,four)) == one + two + three + four)
  assert(fold(nil[Nat]) == Zero)

  assert(fold(List(List(one,two),Nil,List(three, four),List(five,six))) == List(one,two,three,four,five,six))

  ////////////////////////////////////////////////////////////////////////////

  assert(fold(List(one,two,three,four))(using natMultMonoid) == one * two * three * four)
  assert(fold(nil[Nat])(using natMultMonoid) == one)

  ////////////////////////////////////////////////////////////////////////////

  assert(summon[Monoid[Option[Nat]]].combine(Some(two),Some(three)) == Some(five))
  assert(summon[Monoid[Option[Nat]]].combine(Some(two),None) == Some(two))
  assert(summon[Monoid[Option[Nat]]].combine(none[Nat],Some(two)) == Some(two))
  assert(summon[Monoid[Option[Nat]]].combine(none[Nat],None) == None)

  assert((some(two) ⨁ None) == Some(two))
  assert((none[Nat] ⨁ Some(two)) == Some(two))
  assert((some(two) ⨁ Some(three)) == Some(five))
  assert((none[Nat] ⨁ None) == None)

  ////////////////////////////////////////////////////////////////////////////

  assert(fold(List(Some(two),None,Some(three))) == Some(five))
  assert(fold(nil[Option[Nat]]) == None)

  assert((List(Some(one),None,Some(three)) ++ List(Some(four),None,Some(six)))
          == List(Some(one),None,Some(three),Some(four),None,Some(six)))
  assert(summon[Monoid[List[Option[Nat]]]].combine(List(Some(one),None,Some(two)),List(Some(three),None,Some(four)))
         == List(Some(one),None,Some(two),Some(three),None,Some(four)))
  assert((List(Some(one),None,Some(two)) ⨁ List(Some(three),None,Some(four)))
          == List(Some(one),None,Some(two),Some(three),None,Some(four)))

  assert(fold(List(Some(one),None,Some(two)) ⨁ List(Some(three),None,Some(four))) == Some(one + two + three + four))

  ////////////////////////////////////////////////////////////////////////////

  assert((some(List(one,two)) ⨁ None ⨁ Some(List(three,four))) == Some(List(one,two,three,four)))

  assert(
    fold(
      fold(
        List(List(Some(one), None, Some(two)),
             List(Some(three), None, Some(four)),
             List(Some(five), None, Some(six)))))
    == Some(one + two + three + four + five + six))

  ////////////////////////////////////////////////////////////////////////////

import Nat.*
import List.*
import Semigroup.*
import Option.{Some,None,some,none}