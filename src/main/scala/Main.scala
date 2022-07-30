
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

////////////////////////////////////////////////////////////////////////////

enum List[+A]:
  case Cons(head: A, tail: List[A])
  case Nil

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
  def zero: A

extension [A](lhs: A)(using m: Monoid[A])
  @targetName("monoidtiefighter")
  def |+|(rhs: A): A = m.combine(lhs,rhs)

given Monoid[Nat] with
  def zero: Nat = Zero
  def combine(x: Nat, y: Nat): Nat = x + y

given ListMonoid[A]: Monoid[List[A]] with
  def zero: List[A] = Nil
  def combine(lhs: List[A], rhs: List[A]): List[A] = lhs ++ rhs

def fold[A](as: List[A])(using ma: Monoid[A]): A = as match
  case Nil => ma.zero
  case Cons(a,rest) => ma.combine(a,fold(rest))

given OptionMonoid[M](using m: Monoid[M]): Monoid[Option[M]] with
  def zero: Option[M] = None
  def combine(ox: Option[M], oy: Option[M]): Option[M] = (ox,oy) match
    case (None,_) => oy
    case (_, None) => ox
    case (Some(x),Some(y)) => Some(x |+| y)

extension [A](lhs: Option[A])(using m: Monoid[Option[A]])
  @targetName("optionmonoidtiefighter")
  def |+|(rhs: Option[A]): Option[A] = m.combine(lhs,rhs)

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

  val ten = five + five

  val numbers: List[Nat] =
    Cons(one, Cons(two, Nil))

  val moreNumbers: List[Nat] =
    Cons(three, Cons(four, Nil))

  val allNumbers = Cons(one, Cons(two, Cons(three, Cons(four, Nil))))

  assert(numbers ++ moreNumbers == allNumbers)

  assert((Some(two) |+| Some(three)) == Some(five))

  val optionalNumbers: List[Option[Nat]] =
    Cons(Some(two),
      Cons(None,
        Cons(Some(three),
          Nil)))

  val moreOptionalNumbers: List[Option[Nat]] =
    Cons(Some(one),
      Cons(None,
        Cons(Some(four),
          Nil)))

  val allOptionalNumbers: List[Option[Nat]] =
    Cons(Some(two),
      Cons(None,
        Cons(Some(three),
          Cons(Some(one),
            Cons(None,
              Cons(Some(four),
                Nil))))))

  val yetMoreOptionalNumbers: List[Option[Nat]] =
    Cons(Some(five),
      Cons(None,
        Cons(Some(six),
          Nil)))

  val twentyOne = five + five + five + six

  assert(fold(optionalNumbers) == Some(five))

  assert((optionalNumbers |+| moreOptionalNumbers) == allOptionalNumbers)

  assert(fold(allOptionalNumbers) == Some(ten))

  val listsOfOptionalNumbers = Cons(optionalNumbers,Cons(moreOptionalNumbers,Cons(yetMoreOptionalNumbers,Nil)))

  assert(fold(fold(listsOfOptionalNumbers)) == Some(twentyOne))