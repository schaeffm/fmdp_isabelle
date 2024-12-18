object Uint32 {

def less(x: Int, y: Int) : Boolean =
  if (x < 0) y < 0 && x < y
  else y < 0 || x < y

def less_eq(x: Int, y: Int) : Boolean =
  if (x < 0) y < 0 && x <= y
  else y < 0 || x <= y

def set_bit(x: Int, n: BigInt, b: Boolean) : Int =
  if (b)
    x | (1 << n.intValue)
  else
    x & (1 << n.intValue).unary_~

def shiftl(x: Int, n: BigInt) : Int = x << n.intValue

def shiftr(x: Int, n: BigInt) : Int = x >>> n.intValue

def shiftr_signed(x: Int, n: BigInt) : Int = x >> n.intValue

def test_bit(x: Int, n: BigInt) : Boolean =
  (x & (1 << n.intValue)) != 0

} /* object Uint32 */

object Uint64 {

def less(x: Long, y: Long) : Boolean =
  if (x < 0) y < 0 && x < y
  else y < 0 || x < y

def less_eq(x: Long, y: Long) : Boolean =
  if (x < 0) y < 0 && x <= y
  else y < 0 || x <= y

def set_bit(x: Long, n: BigInt, b: Boolean) : Long =
  if (b)
    x | (1L << n.intValue)
  else
    x & (1L << n.intValue).unary_~

def shiftl(x: Long, n: BigInt) : Long = x << n.intValue

def shiftr(x: Long, n: BigInt) : Long = x >>> n.intValue

def shiftr_signed(x: Long, n: BigInt) : Long = x >> n.intValue

def test_bit(x: Long, n: BigInt) : Boolean =
  (x & (1L << n.intValue)) != 0

} /* object Uint64 */


object Array {
  class T[A](n: Int) {
    val array: Array[AnyRef] = new Array[AnyRef](n)
    def apply(i: Int): A = array(i).asInstanceOf[A]
    def update(i: Int, x: A): Unit = array(i) = x.asInstanceOf[AnyRef]
    def length: Int = array.length
    def toList: List[A] = array.toList.asInstanceOf[List[A]]
    override def toString: String = array.mkString("Array.T(", ",", ")")
  }
  def init[A](n: Int)(f: Int => A): T[A] = {
    val a = new T[A](n)
    for (i <- 0 until n) a(i) = f(i)
    a
  }
  def init_list[A](list: List[A]): T[A] = {
    val n = list.length
    val a = new T[A](n)
    var i = 0
    for (x <- list) {
      a(i) = x
      i += 1
    }
    a
  }
  def make[A](n: BigInt)(f: BigInt => A): T[A] = init(n.toInt)((i: Int) => f(BigInt(i)))
  def copy[A](a: T[A]): T[A] = init(a.length)(i => a(i))
  def alloc[A](n: BigInt)(x: A): T[A] = init(n.toInt)(_ => x)
  def len[A](a: T[A]): BigInt = BigInt(a.length)
  def nth[A](a: T[A], n: BigInt): A = a(n.toInt)
  def upd[A](a: T[A], n: BigInt, x: A): Unit = a.update(n.toInt, x)
  def freeze[A](a: T[A]): List[A] = a.toList
}

object DiffArray {

  protected abstract sealed class DiffArray_D[A]

  final case class Current[A] (a:Array.T[AnyRef]) extends DiffArray_D[A]

  final case class Upd[A] (i:Int, v:A, n:DiffArray_D[A]) extends DiffArray_D[A]

  object DiffArray_Realizer {
    def realize[A](a:DiffArray_D[A]): Array.T[AnyRef] = a match {
      case Current(a) => Array.copy(a)
      case Upd(j,v,n) => {val a = realize(n); a.update(j, v.asInstanceOf[AnyRef]); a}
    }
  }

  class T[A] (var d:DiffArray_D[A]) {
    def realize (): Array.T[AnyRef] = { val a=DiffArray_Realizer.realize(d); d = Current(a); a }

    override def toString() = Array.freeze(realize()).toString

    override def equals(obj:Any) =
      if (obj.isInstanceOf[T[A]]) obj.asInstanceOf[T[A]].realize().equals(realize())
      else false

  }


  def array_of_list[A](l : List[A]) : T[A] = new T(Current(Array.init_list(l.asInstanceOf[List[AnyRef]])))
  def new_array[A](v: A, sz: BigInt) = new T[A](Current[A](Array.alloc[AnyRef](sz.intValue)(v.asInstanceOf[AnyRef])))

  private def length[A](a:DiffArray_D[A]) : BigInt = a match {
    case Current(a) => a.length
    case Upd(_,_,n) => length(n)
  }

  def length[A](a : T[A]) : BigInt = length(a.d)

  private def sub[A](a:DiffArray_D[A], i:Int) : A = a match {
    case Current(a) => a(i).asInstanceOf[A]
    case Upd(j,v,n) => if (i==j) v else sub(n,i)
  }

  def get[A](a:T[A], i:BigInt) : A = sub(a.d,i.intValue)

  private def realize[A](a:DiffArray_D[A]): Array.T[AnyRef] = DiffArray_Realizer.realize[A](a)

  def set[A](a:T[A], i:BigInt,v:A) : T[A] = a.d match {
    case Current(ad) => {
      val ii = i.intValue;
      a.d = Upd(ii,ad(ii).asInstanceOf[A],a.d);
      //ad.update(ii,v);
      ad(ii)=v.asInstanceOf[AnyRef]
      new T[A](Current(ad))
    }
    case Upd(_,_,_) => set(new T[A](Current(realize(a.d))), i.intValue,v)
  }

  def grow[A](a:T[A], sz:BigInt, v:A) : T[A] = a.d match {
    case Current(ad) => {
      val n = ad.length
      val adt = Array.init[AnyRef](sz.intValue)(i => if (i < n) ad(i) else v.asInstanceOf[AnyRef])
      new T[A](Current[A](adt))
    }
    case Upd (_,_,_) =>  {
      val ad = realize(a.d)
      val n = ad.length
      val adt = Array.init[AnyRef](sz.intValue)(i => if (i < n) ad(i) else v.asInstanceOf[AnyRef])
      new T[A](Current[A](adt))
    }
  }

  def shrink[A](a:T[A], sz:BigInt) : T[A] =
    if (sz==0) {
      array_of_list(Nil)
    } else {
      a.d match {
        case Current(ad) => {
          val adt = Array.init[AnyRef](sz.intValue)(i => ad(i));
          new T[A](Current[A](adt))
        }
        case Upd (_,_,_) =>  {
          val ad = realize(a.d);
          val adt = Array.init[AnyRef](sz.intValue)(i => ad(i));
          new T[A](Current[A](adt))
        }
      }
    }

  def get_oo[A](d: => A, a:T[A], i:BigInt):A = try get(a,i) catch {
    case _:scala.IndexOutOfBoundsException => d
  }

  def set_oo[A](d: Unit => T[A], a:T[A], i:BigInt, v:A) : T[A] = try set(a,i,v) catch {
    case _:scala.IndexOutOfBoundsException => d(())
  }

}

/*
object Test {



  def assert (b : Boolean) : Unit = if (b) () else throw new java.lang.AssertionError("Assertion Failed")

  def eql[A] (a:DiffArray.T[A], b:List[A]) = assert (a.realize.corresponds(b)((x,y) => x.equals(y)))


  def tests1(): Unit = {
    val a = DiffArray.array_of_list(1::2::3::4::Nil)
      eql(a,1::2::3::4::Nil)

    // Simple update
    val b = DiffArray.set(a,2,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)

    // Another update
    val c = DiffArray.set(b,3,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::9::9::Nil)

    // Update of old version (forces realize)
    val d = DiffArray.set(b,2,8)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::9::9::Nil)
      eql(d,1::2::8::4::Nil)

    }

  def tests2(): Unit = {
    val a = DiffArray.array_of_list(1::2::3::4::Nil)
      eql(a,1::2::3::4::Nil)

    // Simple update
    val b = DiffArray.set(a,2,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)

    // Grow of current version
    val c = DiffArray.grow(b,6,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::9::4::9::9::Nil)

    // Grow of old version
    val d = DiffArray.grow(a,6,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::9::4::9::9::Nil)
      eql(d,1::2::3::4::9::9::Nil)

  }

  def tests3(): Unit = {
    val a = DiffArray.array_of_list(1::2::3::4::Nil)
      eql(a,1::2::3::4::Nil)

    // Simple update
    val b = DiffArray.set(a,2,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)

    // Shrink of current version
    val c = DiffArray.shrink(b,3)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::9::Nil)

    // Shrink of old version
    val d = DiffArray.shrink(a,3)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::9::Nil)
      eql(d,1::2::3::Nil)

  }

  def tests4(): Unit = {
    val a = DiffArray.array_of_list(1::2::3::4::Nil)
      eql(a,1::2::3::4::Nil)

    // Update _oo (succeeds)
    val b = DiffArray.set_oo((_) => a,a,2,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)

    // Update _oo (current version,fails)
    val c = DiffArray.set_oo((_) => a,b,5,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::3::4::Nil)

    // Update _oo (old version,fails)
    val d = DiffArray.set_oo((_) => b,a,5,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::3::4::Nil)
      eql(d,1::2::9::4::Nil)

  }

  def tests5(): Unit = {
    val a = DiffArray.array_of_list(1::2::3::4::Nil)
      eql(a,1::2::3::4::Nil)

    // Update
    val b = DiffArray.set(a,2,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)

    // Get_oo (current version, succeeds)
      assert (DiffArray.get_oo(0,b,2)==9)
    // Get_oo (current version, fails)
      assert (DiffArray.get_oo(0,b,5)==0)
    // Get_oo (old version, succeeds)
      assert (DiffArray.get_oo(0,a,2)==3)
    // Get_oo (old version, fails)
      assert (DiffArray.get_oo(0,a,5)==0)

  }




  def main(args: Array[String]): Unit = {
    tests1 ()
    tests2 ()
    tests3 ()
    tests4 ()
    tests5 ()


    Console.println("Tests passed")
  }

}*/



object Integer_Bit {

def testBit(x: BigInt, n: BigInt) : Boolean =
  if (n.isValidInt)
    x.testBit(n.toInt)
  else
    sys.error("Bit index too large: " + n.toString)

def setBit(x: BigInt, n: BigInt, b: Boolean) : BigInt =
  if (n.isValidInt)
    if (b)
      x.setBit(n.toInt)
    else
      x.clearBit(n.toInt)
  else
    sys.error("Bit index too large: " + n.toString)

def shiftl(x: BigInt, n: BigInt) : BigInt =
  if (n.isValidInt)
    x << n.toInt
  else
    sys.error("Shift index too large: " + n.toString)

def shiftr(x: BigInt, n: BigInt) : BigInt =
  if (n.isValidInt)
    x << n.toInt
  else
    sys.error("Shift index too large: " + n.toString)

} /* object Integer_Bit */

object Solver {

abstract sealed class int
final case class int_of_integer(a: BigInt) extends int

def integer_of_int(x0: int): BigInt = x0 match {
  case int_of_integer(k) => k
}

def equal_inta(k: int, l: int): Boolean = integer_of_int(k) == integer_of_int(l)

trait equal[A] {
  val `Solver.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`Solver.equal`(a, b)
object equal {
  implicit def
    `Solver.equal_var_code`[A : equal, B : equal]: equal[var_code[A, B]] = new
    equal[var_code[A, B]] {
    val `Solver.equal` = (a: var_code[A, B], b: var_code[A, B]) =>
      equal_var_codea[A, B](a, b)
  }
  implicit def `Solver.equal_unit`: equal[Unit] = new equal[Unit] {
    val `Solver.equal` = (a: Unit, b: Unit) => equal_unita(a, b)
  }
  implicit def `Solver.equal_prod`[A : equal, B : equal]: equal[(A, B)] = new
    equal[(A, B)] {
    val `Solver.equal` = (a: (A, B), b: (A, B)) => equal_proda[A, B](a, b)
  }
  implicit def `Solver.equal_option`[A : equal]: equal[Option[A]] = new
    equal[Option[A]] {
    val `Solver.equal` = (a: Option[A], b: Option[A]) => equal_optiona[A](a, b)
  }
  implicit def `Solver.equal_list`[A : equal]: equal[List[A]] = new
    equal[List[A]] {
    val `Solver.equal` = (a: List[A], b: List[A]) => equal_lista[A](a, b)
  }
  implicit def `Solver.equal_bool`: equal[Boolean] = new equal[Boolean] {
    val `Solver.equal` = (a: Boolean, b: Boolean) => equal_boola(a, b)
  }
  implicit def `Solver.equal_nat`: equal[nat] = new equal[nat] {
    val `Solver.equal` = (a: nat, b: nat) => equal_nata(a, b)
  }
  implicit def `Solver.equal_int`: equal[int] = new equal[int] {
    val `Solver.equal` = (a: int, b: int) => equal_inta(a, b)
  }
}

abstract sealed class nat
final case class Nat(a: BigInt) extends nat

def integer_of_nat(x0: nat): BigInt = x0 match {
  case Nat(x) => x
}

def equal_nata(m: nat, n: nat): Boolean = integer_of_nat(m) == integer_of_nat(n)

def times_nata(m: nat, n: nat): nat = Nat(integer_of_nat(m) * integer_of_nat(n))

trait times[A] {
  val `Solver.times`: (A, A) => A
}
def times[A](a: A, b: A)(implicit A: times[A]): A = A.`Solver.times`(a, b)
object times {
  implicit def `Solver.times_real`: times[real] = new times[real] {
    val `Solver.times` = (a: real, b: real) => times_reala(a, b)
  }
  implicit def `Solver.times_nat`: times[nat] = new times[nat] {
    val `Solver.times` = (a: nat, b: nat) => times_nata(a, b)
  }
}

trait dvd[A] extends times[A] {
}
object dvd {
  implicit def `Solver.dvd_nat`: dvd[nat] = new dvd[nat] {
    val `Solver.times` = (a: nat, b: nat) => times_nata(a, b)
  }
}

def apsnd[A, B, C](f: A => B, x1: (C, A)): (C, B) = (f, x1) match {
  case (f, (x, y)) => (x, f(y))
}

abstract sealed class num
final case class One() extends num
final case class Bit0(a: num) extends num
final case class Bit1(a: num) extends num

def divmod_integer(k: BigInt, l: BigInt): (BigInt, BigInt) =
  (if (k == BigInt(0)) (BigInt(0), BigInt(0))
    else (if (BigInt(0) < l)
           (if (BigInt(0) < k)
             ((k: BigInt) => (l: BigInt) => if (l == 0) (BigInt(0), k) else
               (k /% l)).apply(k).apply(l)
             else {
                    val (r, s) =
                      ((k: BigInt) => (l: BigInt) => if (l == 0)
                        (BigInt(0), k) else (k /% l)).apply((- k)).apply(l):
                        ((BigInt, BigInt));
                    (if (s == BigInt(0)) ((- r), BigInt(0))
                      else ((- r) - BigInt(1), l - s))
                  })
           else (if (l == BigInt(0)) (BigInt(0), k)
                  else apsnd[BigInt, BigInt,
                              BigInt](((a: BigInt) => (- a)),
                                       (if (k < BigInt(0))
 ((k: BigInt) => (l: BigInt) => if (l == 0) (BigInt(0), k) else
   (k /% l)).apply((- k)).apply((- l))
 else {
        val (r, s) =
          ((k: BigInt) => (l: BigInt) => if (l == 0) (BigInt(0), k) else
            (k /% l)).apply(k).apply((- l)):
            ((BigInt, BigInt));
        (if (s == BigInt(0)) ((- r), BigInt(0))
          else ((- r) - BigInt(1), (- l) - s))
      })))))

def snd[A, B](x0: (A, B)): B = x0 match {
  case (x1, x2) => x2
}

def modulo_integer(k: BigInt, l: BigInt): BigInt =
  snd[BigInt, BigInt](divmod_integer(k, l))

def modulo_nata(m: nat, n: nat): nat =
  Nat(modulo_integer(integer_of_nat(m), integer_of_nat(n)))

def fst[A, B](x0: (A, B)): A = x0 match {
  case (x1, x2) => x1
}

def divide_integer(k: BigInt, l: BigInt): BigInt =
  fst[BigInt, BigInt](divmod_integer(k, l))

def divide_nata(m: nat, n: nat): nat =
  Nat(divide_integer(integer_of_nat(m), integer_of_nat(n)))

trait ord[A] {
  val `Solver.less_eq`: (A, A) => Boolean
  val `Solver.less`: (A, A) => Boolean
}
def less_eq[A](a: A, b: A)(implicit A: ord[A]): Boolean =
  A.`Solver.less_eq`(a, b)
def less[A](a: A, b: A)(implicit A: ord[A]): Boolean = A.`Solver.less`(a, b)
object ord {
  implicit def `Solver.ord_integer`: ord[BigInt] = new ord[BigInt] {
    val `Solver.less_eq` = (a: BigInt, b: BigInt) => a <= b
    val `Solver.less` = (a: BigInt, b: BigInt) => a < b
  }
  implicit def `Solver.ord_ereal`: ord[ereal] = new ord[ereal] {
    val `Solver.less_eq` = (a: ereal, b: ereal) => less_eq_ereal(a, b)
    val `Solver.less` = (a: ereal, b: ereal) => less_ereal(a, b)
  }
  implicit def `Solver.ord_real`: ord[real] = new ord[real] {
    val `Solver.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `Solver.less` = (a: real, b: real) => less_real(a, b)
  }
  implicit def `Solver.ord_nat`: ord[nat] = new ord[nat] {
    val `Solver.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
    val `Solver.less` = (a: nat, b: nat) => less_nat(a, b)
  }
}

def max[A : ord](a: A, b: A): A = (if (less_eq[A](a, b)) b else a)

def nat_of_integer(k: BigInt): nat = Nat(max[BigInt](BigInt(0), k))

def zero_nata: nat = Nat(BigInt(0))

def one_nata: nat = Nat(BigInt(1))

abstract sealed class char
final case class Char(a: Boolean, b: Boolean, c: Boolean, d: Boolean,
                       e: Boolean, f: Boolean, g: Boolean, h: Boolean)
  extends char

def string_of_digit(n: nat): List[char] =
  (if (equal_nata(n, zero_nata))
    List(Char(false, false, false, false, true, true, false, false))
    else (if (equal_nata(n, one_nata))
           List(Char(true, false, false, false, true, true, false, false))
           else (if (equal_nata(n, nat_of_integer(BigInt(2))))
                  List(Char(false, true, false, false, true, true, false,
                             false))
                  else (if (equal_nata(n, nat_of_integer(BigInt(3))))
                         List(Char(true, true, false, false, true, true, false,
                                    false))
                         else (if (equal_nata(n, nat_of_integer(BigInt(4))))
                                List(Char(false, false, true, false, true, true,
   false, false))
                                else (if (equal_nata(n,
              nat_of_integer(BigInt(5))))
                                       List(Char(true, false, true, false, true,
          true, false, false))
                                       else (if (equal_nata(n,
                     nat_of_integer(BigInt(6))))
      List(Char(false, true, true, false, true, true, false, false))
      else (if (equal_nata(n, nat_of_integer(BigInt(7))))
             List(Char(true, true, true, false, true, true, false, false))
             else (if (equal_nata(n, nat_of_integer(BigInt(8))))
                    List(Char(false, false, false, true, true, true, false,
                               false))
                    else List(Char(true, false, false, true, true, true, false,
                                    false)))))))))))

def less_nat(m: nat, n: nat): Boolean = integer_of_nat(m) < integer_of_nat(n)

def shows_string: (List[char]) => (List[char]) => List[char] =
  ((a: List[char]) => (b: List[char]) => a ++ b)

def comp[A, B, C](f: A => B, g: C => A): C => B = ((x: C) => f(g(x)))

def showsp_nat(p: nat, n: nat): (List[char]) => List[char] =
  (if (less_nat(n, nat_of_integer(BigInt(10))))
    shows_string.apply(string_of_digit(n))
    else comp[List[char], List[char],
               List[char]](showsp_nat(p, divide_nata(n,
              nat_of_integer(BigInt(10)))),
                            shows_string.apply(string_of_digit(modulo_nata(n,
                                    nat_of_integer(BigInt(10)))))))

def shows_prec_nat: nat => nat => (List[char]) => List[char] =
  ((a: nat) => (b: nat) => showsp_nat(a, b))

def shows_sep[A](s: A => (List[char]) => List[char],
                  sep: (List[char]) => List[char], x2: List[A]):
      (List[char]) => List[char]
  =
  (s, sep, x2) match {
  case (s, sep, Nil) => shows_string.apply(Nil)
  case (s, sep, List(x)) => s(x)
  case (s, sep, x :: v :: va) =>
    comp[List[char], List[char],
          List[char]](comp[List[char], List[char], List[char]](s(x), sep),
                       shows_sep[A](s, sep, v :: va))
}

def nulla[A](x0: List[A]): Boolean = x0 match {
  case Nil => true
  case x :: xs => false
}

def shows_list_gen[A](showsx: A => (List[char]) => List[char], e: List[char],
                       l: List[char], s: List[char], r: List[char],
                       xs: List[A]):
      (List[char]) => List[char]
  =
  (if (nulla[A](xs)) shows_string.apply(e)
    else comp[List[char], List[char],
               List[char]](comp[List[char], List[char],
                                 List[char]](shows_string.apply(l),
      shows_sep[A](showsx, shows_string.apply(s), xs)),
                            shows_string.apply(r)))

def showsp_list[A](s: nat => A => (List[char]) => List[char], p: nat,
                    xs: List[A]):
      (List[char]) => List[char]
  =
  shows_list_gen[A](s(zero_nata),
                     List(Char(true, true, false, true, true, false, true,
                                false),
                           Char(true, false, true, true, true, false, true,
                                 false)),
                     List(Char(true, true, false, true, true, false, true,
                                false)),
                     List(Char(false, false, true, true, false, true, false,
                                false),
                           Char(false, false, false, false, false, true, false,
                                 false)),
                     List(Char(true, false, true, true, true, false, true,
                                false)),
                     xs)

def shows_list_nat: (List[nat]) => (List[char]) => List[char] =
  ((a: List[nat]) => showsp_list[nat](shows_prec_nat, zero_nata, a))

trait show[A] {
  val `Solver.shows_prec`: (nat, A, List[char]) => List[char]
  val `Solver.shows_list`: (List[A], List[char]) => List[char]
}
def shows_prec[A](a: nat, b: A, c: List[char])(implicit A: show[A]): List[char]
  = A.`Solver.shows_prec`(a, b, c)
def shows_list[A](a: List[A], b: List[char])(implicit A: show[A]): List[char] =
  A.`Solver.shows_list`(a, b)
object show {
  implicit def `Solver.show_real`: show[real] = new show[real] {
    val `Solver.shows_prec` = (a: nat, b: real, c: List[char]) =>
      shows_prec_real.apply(a).apply(b).apply(c)
    val `Solver.shows_list` = (a: List[real], b: List[char]) =>
      shows_list_real.apply(a).apply(b)
  }
  implicit def `Solver.show_bool`: show[Boolean] = new show[Boolean] {
    val `Solver.shows_prec` = (a: nat, b: Boolean, c: List[char]) =>
      shows_prec_bool.apply(a).apply(b).apply(c)
    val `Solver.shows_list` = (a: List[Boolean], b: List[char]) =>
      shows_list_bool.apply(a).apply(b)
  }
  implicit def `Solver.show_nat`: show[nat] = new show[nat] {
    val `Solver.shows_prec` = (a: nat, b: nat, c: List[char]) =>
      shows_prec_nat.apply(a).apply(b).apply(c)
    val `Solver.shows_list` = (a: List[nat], b: List[char]) =>
      shows_list_nat.apply(a).apply(b)
  }
}

trait one[A] {
  val `Solver.one`: A
}
def one[A](implicit A: one[A]): A = A.`Solver.one`
object one {
  implicit def `Solver.one_integer`: one[BigInt] = new one[BigInt] {
    val `Solver.one` = one_integera
  }
  implicit def `Solver.one_real`: one[real] = new one[real] {
    val `Solver.one` = one_reala
  }
  implicit def `Solver.one_nat`: one[nat] = new one[nat] {
    val `Solver.one` = one_nata
  }
}

def plus_nata(m: nat, n: nat): nat = Nat(integer_of_nat(m) + integer_of_nat(n))

trait plus[A] {
  val `Solver.plus`: (A, A) => A
}
def plus[A](a: A, b: A)(implicit A: plus[A]): A = A.`Solver.plus`(a, b)
object plus {
  implicit def `Solver.plus_ereal`: plus[ereal] = new plus[ereal] {
    val `Solver.plus` = (a: ereal, b: ereal) => plus_ereala(a, b)
  }
  implicit def `Solver.plus_real`: plus[real] = new plus[real] {
    val `Solver.plus` = (a: real, b: real) => plus_reala(a, b)
  }
  implicit def `Solver.plus_nat`: plus[nat] = new plus[nat] {
    val `Solver.plus` = (a: nat, b: nat) => plus_nata(a, b)
  }
}

trait zero[A] {
  val `Solver.zero`: A
}
def zero[A](implicit A: zero[A]): A = A.`Solver.zero`
object zero {
  implicit def `Solver.zero_integer`: zero[BigInt] = new zero[BigInt] {
    val `Solver.zero` = BigInt(0)
  }
  implicit def `Solver.zero_ereal`: zero[ereal] = new zero[ereal] {
    val `Solver.zero` = zero_ereala
  }
  implicit def `Solver.zero_real`: zero[real] = new zero[real] {
    val `Solver.zero` = zero_reala
  }
  implicit def `Solver.zero_nat`: zero[nat] = new zero[nat] {
    val `Solver.zero` = zero_nata
  }
}

trait semigroup_add[A] extends plus[A] {
}
object semigroup_add {
  implicit def `Solver.semigroup_add_ereal`: semigroup_add[ereal] = new
    semigroup_add[ereal] {
    val `Solver.plus` = (a: ereal, b: ereal) => plus_ereala(a, b)
  }
  implicit def `Solver.semigroup_add_real`: semigroup_add[real] = new
    semigroup_add[real] {
    val `Solver.plus` = (a: real, b: real) => plus_reala(a, b)
  }
  implicit def `Solver.semigroup_add_nat`: semigroup_add[nat] = new
    semigroup_add[nat] {
    val `Solver.plus` = (a: nat, b: nat) => plus_nata(a, b)
  }
}

trait numeral[A] extends one[A] with semigroup_add[A] {
}
object numeral {
  implicit def `Solver.numeral_nat`: numeral[nat] = new numeral[nat] {
    val `Solver.plus` = (a: nat, b: nat) => plus_nata(a, b)
    val `Solver.one` = one_nata
  }
}

trait power[A] extends one[A] with times[A] {
}
object power {
  implicit def `Solver.power_real`: power[real] = new power[real] {
    val `Solver.times` = (a: real, b: real) => times_reala(a, b)
    val `Solver.one` = one_reala
  }
  implicit def `Solver.power_nat`: power[nat] = new power[nat] {
    val `Solver.times` = (a: nat, b: nat) => times_nata(a, b)
    val `Solver.one` = one_nata
  }
}

def minus_nata(m: nat, n: nat): nat =
  Nat(max[BigInt](BigInt(0), integer_of_nat(m) - integer_of_nat(n)))

trait minus[A] {
  val `Solver.minus`: (A, A) => A
}
def minus[A](a: A, b: A)(implicit A: minus[A]): A = A.`Solver.minus`(a, b)
object minus {
  implicit def `Solver.minus_real`: minus[real] = new minus[real] {
    val `Solver.minus` = (a: real, b: real) => minus_reala(a, b)
  }
  implicit def `Solver.minus_nat`: minus[nat] = new minus[nat] {
    val `Solver.minus` = (a: nat, b: nat) => minus_nata(a, b)
  }
}

trait divide[A] {
  val `Solver.divide`: (A, A) => A
}
def divide[A](a: A, b: A)(implicit A: divide[A]): A = A.`Solver.divide`(a, b)
object divide {
  implicit def `Solver.divide_nat`: divide[nat] = new divide[nat] {
    val `Solver.divide` = (a: nat, b: nat) => divide_nata(a, b)
  }
}

trait modulo[A] extends divide[A] with dvd[A] {
  val `Solver.modulo`: (A, A) => A
}
def modulo[A](a: A, b: A)(implicit A: modulo[A]): A = A.`Solver.modulo`(a, b)
object modulo {
  implicit def `Solver.modulo_nat`: modulo[nat] = new modulo[nat] {
    val `Solver.modulo` = (a: nat, b: nat) => modulo_nata(a, b)
    val `Solver.times` = (a: nat, b: nat) => times_nata(a, b)
    val `Solver.divide` = (a: nat, b: nat) => divide_nata(a, b)
  }
}

def less_eq_nat(m: nat, n: nat): Boolean =
  integer_of_nat(m) <= integer_of_nat(n)

trait ab_semigroup_add[A] extends semigroup_add[A] {
}
object ab_semigroup_add {
  implicit def `Solver.ab_semigroup_add_nat`: ab_semigroup_add[nat] = new
    ab_semigroup_add[nat] {
    val `Solver.plus` = (a: nat, b: nat) => plus_nata(a, b)
  }
}

trait monoid_add[A] extends semigroup_add[A] with zero[A] {
}
object monoid_add {
  implicit def `Solver.monoid_add_ereal`: monoid_add[ereal] = new
    monoid_add[ereal] {
    val `Solver.zero` = zero_ereala
    val `Solver.plus` = (a: ereal, b: ereal) => plus_ereala(a, b)
  }
  implicit def `Solver.monoid_add_real`: monoid_add[real] = new monoid_add[real]
    {
    val `Solver.zero` = zero_reala
    val `Solver.plus` = (a: real, b: real) => plus_reala(a, b)
  }
  implicit def `Solver.monoid_add_nat`: monoid_add[nat] = new monoid_add[nat] {
    val `Solver.zero` = zero_nata
    val `Solver.plus` = (a: nat, b: nat) => plus_nata(a, b)
  }
}

trait comm_monoid_add[A] extends ab_semigroup_add[A] with monoid_add[A] {
}
object comm_monoid_add {
  implicit def `Solver.comm_monoid_add_nat`: comm_monoid_add[nat] = new
    comm_monoid_add[nat] {
    val `Solver.zero` = zero_nata
    val `Solver.plus` = (a: nat, b: nat) => plus_nata(a, b)
  }
}

trait mult_zero[A] extends times[A] with zero[A] {
}
object mult_zero {
  implicit def `Solver.mult_zero_nat`: mult_zero[nat] = new mult_zero[nat] {
    val `Solver.zero` = zero_nata
    val `Solver.times` = (a: nat, b: nat) => times_nata(a, b)
  }
}

trait semigroup_mult[A] extends times[A] {
}
object semigroup_mult {
  implicit def `Solver.semigroup_mult_real`: semigroup_mult[real] = new
    semigroup_mult[real] {
    val `Solver.times` = (a: real, b: real) => times_reala(a, b)
  }
  implicit def `Solver.semigroup_mult_nat`: semigroup_mult[nat] = new
    semigroup_mult[nat] {
    val `Solver.times` = (a: nat, b: nat) => times_nata(a, b)
  }
}

trait semiring[A] extends ab_semigroup_add[A] with semigroup_mult[A] {
}
object semiring {
  implicit def `Solver.semiring_nat`: semiring[nat] = new semiring[nat] {
    val `Solver.times` = (a: nat, b: nat) => times_nata(a, b)
    val `Solver.plus` = (a: nat, b: nat) => plus_nata(a, b)
  }
}

trait semiring_0[A]
  extends comm_monoid_add[A] with mult_zero[A] with semiring[A] {
}
object semiring_0 {
  implicit def `Solver.semiring_0_nat`: semiring_0[nat] = new semiring_0[nat] {
    val `Solver.times` = (a: nat, b: nat) => times_nata(a, b)
    val `Solver.zero` = zero_nata
    val `Solver.plus` = (a: nat, b: nat) => plus_nata(a, b)
  }
}

trait semiring_no_zero_divisors[A] extends semiring_0[A] {
}
object semiring_no_zero_divisors {
  implicit def
    `Solver.semiring_no_zero_divisors_nat`: semiring_no_zero_divisors[nat] = new
    semiring_no_zero_divisors[nat] {
    val `Solver.times` = (a: nat, b: nat) => times_nata(a, b)
    val `Solver.zero` = zero_nata
    val `Solver.plus` = (a: nat, b: nat) => plus_nata(a, b)
  }
}

trait monoid_mult[A] extends semigroup_mult[A] with power[A] {
}
object monoid_mult {
  implicit def `Solver.monoid_mult_real`: monoid_mult[real] = new
    monoid_mult[real] {
    val `Solver.one` = one_reala
    val `Solver.times` = (a: real, b: real) => times_reala(a, b)
  }
  implicit def `Solver.monoid_mult_nat`: monoid_mult[nat] = new monoid_mult[nat]
    {
    val `Solver.one` = one_nata
    val `Solver.times` = (a: nat, b: nat) => times_nata(a, b)
  }
}

trait semiring_numeral[A]
  extends monoid_mult[A] with numeral[A] with semiring[A] {
}
object semiring_numeral {
  implicit def `Solver.semiring_numeral_nat`: semiring_numeral[nat] = new
    semiring_numeral[nat] {
    val `Solver.plus` = (a: nat, b: nat) => plus_nata(a, b)
    val `Solver.one` = one_nata
    val `Solver.times` = (a: nat, b: nat) => times_nata(a, b)
  }
}

trait zero_neq_one[A] extends one[A] with zero[A] {
}
object zero_neq_one {
  implicit def `Solver.zero_neq_one_integer`: zero_neq_one[BigInt] = new
    zero_neq_one[BigInt] {
    val `Solver.zero` = BigInt(0)
    val `Solver.one` = one_integera
  }
  implicit def `Solver.zero_neq_one_nat`: zero_neq_one[nat] = new
    zero_neq_one[nat] {
    val `Solver.zero` = zero_nata
    val `Solver.one` = one_nata
  }
}

trait semiring_1[A]
  extends semiring_numeral[A] with semiring_0[A] with zero_neq_one[A] {
}
object semiring_1 {
  implicit def `Solver.semiring_1_nat`: semiring_1[nat] = new semiring_1[nat] {
    val `Solver.zero` = zero_nata
    val `Solver.one` = one_nata
    val `Solver.times` = (a: nat, b: nat) => times_nata(a, b)
    val `Solver.plus` = (a: nat, b: nat) => plus_nata(a, b)
  }
}

trait semiring_1_no_zero_divisors[A]
  extends semiring_1[A] with semiring_no_zero_divisors[A] {
}
object semiring_1_no_zero_divisors {
  implicit def
    `Solver.semiring_1_no_zero_divisors_nat`: semiring_1_no_zero_divisors[nat] =
    new semiring_1_no_zero_divisors[nat] {
    val `Solver.one` = one_nata
    val `Solver.times` = (a: nat, b: nat) => times_nata(a, b)
    val `Solver.zero` = zero_nata
    val `Solver.plus` = (a: nat, b: nat) => plus_nata(a, b)
  }
}

trait cancel_semigroup_add[A] extends semigroup_add[A] {
}
object cancel_semigroup_add {
  implicit def `Solver.cancel_semigroup_add_nat`: cancel_semigroup_add[nat] =
    new cancel_semigroup_add[nat] {
    val `Solver.plus` = (a: nat, b: nat) => plus_nata(a, b)
  }
}

trait cancel_ab_semigroup_add[A]
  extends ab_semigroup_add[A] with cancel_semigroup_add[A] with minus[A] {
}
object cancel_ab_semigroup_add {
  implicit def
    `Solver.cancel_ab_semigroup_add_nat`: cancel_ab_semigroup_add[nat] = new
    cancel_ab_semigroup_add[nat] {
    val `Solver.minus` = (a: nat, b: nat) => minus_nata(a, b)
    val `Solver.plus` = (a: nat, b: nat) => plus_nata(a, b)
  }
}

trait cancel_comm_monoid_add[A]
  extends cancel_ab_semigroup_add[A] with comm_monoid_add[A] {
}
object cancel_comm_monoid_add {
  implicit def `Solver.cancel_comm_monoid_add_nat`: cancel_comm_monoid_add[nat]
    = new cancel_comm_monoid_add[nat] {
    val `Solver.zero` = zero_nata
    val `Solver.minus` = (a: nat, b: nat) => minus_nata(a, b)
    val `Solver.plus` = (a: nat, b: nat) => plus_nata(a, b)
  }
}

trait semiring_0_cancel[A] extends cancel_comm_monoid_add[A] with semiring_0[A]
  {
}
object semiring_0_cancel {
  implicit def `Solver.semiring_0_cancel_nat`: semiring_0_cancel[nat] = new
    semiring_0_cancel[nat] {
    val `Solver.times` = (a: nat, b: nat) => times_nata(a, b)
    val `Solver.zero` = zero_nata
    val `Solver.minus` = (a: nat, b: nat) => minus_nata(a, b)
    val `Solver.plus` = (a: nat, b: nat) => plus_nata(a, b)
  }
}

trait ab_semigroup_mult[A] extends semigroup_mult[A] {
}
object ab_semigroup_mult {
  implicit def `Solver.ab_semigroup_mult_nat`: ab_semigroup_mult[nat] = new
    ab_semigroup_mult[nat] {
    val `Solver.times` = (a: nat, b: nat) => times_nata(a, b)
  }
}

trait comm_semiring[A] extends ab_semigroup_mult[A] with semiring[A] {
}
object comm_semiring {
  implicit def `Solver.comm_semiring_nat`: comm_semiring[nat] = new
    comm_semiring[nat] {
    val `Solver.plus` = (a: nat, b: nat) => plus_nata(a, b)
    val `Solver.times` = (a: nat, b: nat) => times_nata(a, b)
  }
}

trait comm_semiring_0[A] extends comm_semiring[A] with semiring_0[A] {
}
object comm_semiring_0 {
  implicit def `Solver.comm_semiring_0_nat`: comm_semiring_0[nat] = new
    comm_semiring_0[nat] {
    val `Solver.zero` = zero_nata
    val `Solver.plus` = (a: nat, b: nat) => plus_nata(a, b)
    val `Solver.times` = (a: nat, b: nat) => times_nata(a, b)
  }
}

trait comm_semiring_0_cancel[A]
  extends comm_semiring_0[A] with semiring_0_cancel[A] {
}
object comm_semiring_0_cancel {
  implicit def `Solver.comm_semiring_0_cancel_nat`: comm_semiring_0_cancel[nat]
    = new comm_semiring_0_cancel[nat] {
    val `Solver.minus` = (a: nat, b: nat) => minus_nata(a, b)
    val `Solver.zero` = zero_nata
    val `Solver.plus` = (a: nat, b: nat) => plus_nata(a, b)
    val `Solver.times` = (a: nat, b: nat) => times_nata(a, b)
  }
}

trait semiring_1_cancel[A] extends semiring_0_cancel[A] with semiring_1[A] {
}
object semiring_1_cancel {
  implicit def `Solver.semiring_1_cancel_nat`: semiring_1_cancel[nat] = new
    semiring_1_cancel[nat] {
    val `Solver.one` = one_nata
    val `Solver.times` = (a: nat, b: nat) => times_nata(a, b)
    val `Solver.zero` = zero_nata
    val `Solver.minus` = (a: nat, b: nat) => minus_nata(a, b)
    val `Solver.plus` = (a: nat, b: nat) => plus_nata(a, b)
  }
}

trait comm_monoid_mult[A]
  extends ab_semigroup_mult[A] with monoid_mult[A] with dvd[A] {
}
object comm_monoid_mult {
  implicit def `Solver.comm_monoid_mult_nat`: comm_monoid_mult[nat] = new
    comm_monoid_mult[nat] {
    val `Solver.one` = one_nata
    val `Solver.times` = (a: nat, b: nat) => times_nata(a, b)
  }
}

trait comm_semiring_1[A]
  extends comm_monoid_mult[A] with comm_semiring_0[A] with semiring_1[A] {
}
object comm_semiring_1 {
  implicit def `Solver.comm_semiring_1_nat`: comm_semiring_1[nat] = new
    comm_semiring_1[nat] {
    val `Solver.zero` = zero_nata
    val `Solver.plus` = (a: nat, b: nat) => plus_nata(a, b)
    val `Solver.one` = one_nata
    val `Solver.times` = (a: nat, b: nat) => times_nata(a, b)
  }
}

trait comm_semiring_1_cancel[A]
  extends comm_semiring_0_cancel[A] with comm_semiring_1[A] with
    semiring_1_cancel[A]
  {
}
object comm_semiring_1_cancel {
  implicit def `Solver.comm_semiring_1_cancel_nat`: comm_semiring_1_cancel[nat]
    = new comm_semiring_1_cancel[nat] {
    val `Solver.one` = one_nata
    val `Solver.times` = (a: nat, b: nat) => times_nata(a, b)
    val `Solver.zero` = zero_nata
    val `Solver.minus` = (a: nat, b: nat) => minus_nata(a, b)
    val `Solver.plus` = (a: nat, b: nat) => plus_nata(a, b)
  }
}

trait semidom[A]
  extends comm_semiring_1_cancel[A] with semiring_1_no_zero_divisors[A] {
}
object semidom {
  implicit def `Solver.semidom_nat`: semidom[nat] = new semidom[nat] {
    val `Solver.one` = one_nata
    val `Solver.times` = (a: nat, b: nat) => times_nata(a, b)
    val `Solver.zero` = zero_nata
    val `Solver.minus` = (a: nat, b: nat) => minus_nata(a, b)
    val `Solver.plus` = (a: nat, b: nat) => plus_nata(a, b)
  }
}

trait preorder[A] extends ord[A] {
}
object preorder {
  implicit def `Solver.preorder_real`: preorder[real] = new preorder[real] {
    val `Solver.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `Solver.less` = (a: real, b: real) => less_real(a, b)
  }
  implicit def `Solver.preorder_nat`: preorder[nat] = new preorder[nat] {
    val `Solver.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
    val `Solver.less` = (a: nat, b: nat) => less_nat(a, b)
  }
}

trait order[A] extends preorder[A] {
}
object order {
  implicit def `Solver.order_real`: order[real] = new order[real] {
    val `Solver.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `Solver.less` = (a: real, b: real) => less_real(a, b)
  }
  implicit def `Solver.order_nat`: order[nat] = new order[nat] {
    val `Solver.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
    val `Solver.less` = (a: nat, b: nat) => less_nat(a, b)
  }
}

def ceq_nata: Option[nat => nat => Boolean] =
  Some[nat => nat => Boolean](((a: nat) => (b: nat) => equal_nata(a, b)))

trait ceq[A] {
  val `Solver.ceq`: Option[A => A => Boolean]
}
def ceq[A](implicit A: ceq[A]): Option[A => A => Boolean] = A.`Solver.ceq`
object ceq {
  implicit def `Solver.ceq_prod`[A : ceq, B : ceq]: ceq[(A, B)] = new
    ceq[(A, B)] {
    val `Solver.ceq` = ceq_proda[A, B]
  }
  implicit def `Solver.ceq_iarray`[A : ceq : equal]: ceq[Array.T[A]] = new
    ceq[Array.T[A]] {
    val `Solver.ceq` = ceq_iarraya[A]
  }
  implicit def `Solver.ceq_nat`: ceq[nat] = new ceq[nat] {
    val `Solver.ceq` = ceq_nata
  }
}

abstract sealed class itself[A]
final case class typea[A]() extends itself[A]

def def_hashmap_size_nat: (itself[nat]) => nat =
  ((_: itself[nat]) => nat_of_integer(BigInt(16)))

trait hashable[A] {
  val `Solver.hashcode`: A => Int
  val `Solver.def_hashmap_size`: (itself[A]) => nat
}
def hashcode[A](a: A)(implicit A: hashable[A]): Int = A.`Solver.hashcode`(a)
def def_hashmap_size[A](a: itself[A])(implicit A: hashable[A]): nat =
  A.`Solver.def_hashmap_size`(a)
object hashable {
  implicit def
    `Solver.hashable_var_code`[A : hashable, B : hashable]:
      hashable[var_code[A, B]]
    = new hashable[var_code[A, B]] {
    val `Solver.hashcode` = (a: var_code[A, B]) =>
      hashcode_var_code[A, B].apply(a)
    val `Solver.def_hashmap_size` = (a: itself[var_code[A, B]]) =>
      def_hashmap_size_var_code[A, B].apply(a)
  }
  implicit def
    `Solver.hashable_prod`[A : hashable, B : hashable]: hashable[(A, B)] = new
    hashable[(A, B)] {
    val `Solver.hashcode` = (a: (A, B)) => hashcode_prod[A, B](a)
    val `Solver.def_hashmap_size` = (a: itself[(A, B)]) =>
      def_hashmap_size_prod[A, B].apply(a)
  }
  implicit def `Solver.hashable_option`[A : hashable]: hashable[Option[A]] = new
    hashable[Option[A]] {
    val `Solver.hashcode` = (a: Option[A]) => hashcode_option[A](a)
    val `Solver.def_hashmap_size` = (a: itself[Option[A]]) =>
      def_hashmap_size_option[A].apply(a)
  }
  implicit def `Solver.hashable_list`[A : hashable]: hashable[List[A]] = new
    hashable[List[A]] {
    val `Solver.hashcode` = (a: List[A]) => hashcode_list[A].apply(a)
    val `Solver.def_hashmap_size` = (a: itself[List[A]]) =>
      def_hashmap_size_list[A].apply(a)
  }
  implicit def `Solver.hashable_bool`: hashable[Boolean] = new hashable[Boolean]
    {
    val `Solver.hashcode` = (a: Boolean) => hashcode_bool(a)
    val `Solver.def_hashmap_size` = (a: itself[Boolean]) =>
      def_hashmap_size_bool.apply(a)
  }
  implicit def `Solver.hashable_nat`: hashable[nat] = new hashable[nat] {
    val `Solver.hashcode` = (a: nat) => hashcode_nat(a)
    val `Solver.def_hashmap_size` = (a: itself[nat]) =>
      def_hashmap_size_nat.apply(a)
  }
}

def int_of_nat(n: nat): int = int_of_integer(integer_of_nat(n))

def uint32_of_int(i: int): Int = (integer_of_int(i)).intValue

def hashcode_nat(n: nat): Int = uint32_of_int(int_of_nat(n))

abstract sealed class phantom[A, B]
final case class phantoma[B, A](a: B) extends phantom[A, B]

abstract sealed class set_impla
final case class set_Choose() extends set_impla
final case class set_Collect() extends set_impla
final case class set_DList() extends set_impla
final case class set_RBT() extends set_impla
final case class set_Monad() extends set_impla

def set_impl_nata: phantom[nat, set_impla] = phantoma[set_impla, nat](set_RBT())

trait set_impl[A] {
  val `Solver.set_impl`: phantom[A, set_impla]
}
def set_impl[A](implicit A: set_impl[A]): phantom[A, set_impla] =
  A.`Solver.set_impl`
object set_impl {
  implicit def `Solver.set_impl_iarray`[A]: set_impl[Array.T[A]] = new
    set_impl[Array.T[A]] {
    val `Solver.set_impl` = set_impl_iarraya[A]
  }
  implicit def `Solver.set_impl_nat`: set_impl[nat] = new set_impl[nat] {
    val `Solver.set_impl` = set_impl_nata
  }
}

trait linorder[A] extends order[A] {
}
object linorder {
  implicit def `Solver.linorder_real`: linorder[real] = new linorder[real] {
    val `Solver.less_eq` = (a: real, b: real) => less_eq_real(a, b)
    val `Solver.less` = (a: real, b: real) => less_real(a, b)
  }
  implicit def `Solver.linorder_nat`: linorder[nat] = new linorder[nat] {
    val `Solver.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
    val `Solver.less` = (a: nat, b: nat) => less_nat(a, b)
  }
}

trait semiring_no_zero_divisors_cancel[A] extends semiring_no_zero_divisors[A] {
}
object semiring_no_zero_divisors_cancel {
  implicit def
    `Solver.semiring_no_zero_divisors_cancel_nat`:
      semiring_no_zero_divisors_cancel[nat]
    = new semiring_no_zero_divisors_cancel[nat] {
    val `Solver.times` = (a: nat, b: nat) => times_nata(a, b)
    val `Solver.zero` = zero_nata
    val `Solver.plus` = (a: nat, b: nat) => plus_nata(a, b)
  }
}

trait semidom_divide[A]
  extends divide[A] with semidom[A] with semiring_no_zero_divisors_cancel[A] {
}
object semidom_divide {
  implicit def `Solver.semidom_divide_nat`: semidom_divide[nat] = new
    semidom_divide[nat] {
    val `Solver.minus` = (a: nat, b: nat) => minus_nata(a, b)
    val `Solver.one` = one_nata
    val `Solver.times` = (a: nat, b: nat) => times_nata(a, b)
    val `Solver.zero` = zero_nata
    val `Solver.plus` = (a: nat, b: nat) => plus_nata(a, b)
    val `Solver.divide` = (a: nat, b: nat) => divide_nata(a, b)
  }
}

trait algebraic_semidom[A] extends semidom_divide[A] {
}
object algebraic_semidom {
  implicit def `Solver.algebraic_semidom_nat`: algebraic_semidom[nat] = new
    algebraic_semidom[nat] {
    val `Solver.divide` = (a: nat, b: nat) => divide_nata(a, b)
    val `Solver.minus` = (a: nat, b: nat) => minus_nata(a, b)
    val `Solver.one` = one_nata
    val `Solver.times` = (a: nat, b: nat) => times_nata(a, b)
    val `Solver.zero` = zero_nata
    val `Solver.plus` = (a: nat, b: nat) => plus_nata(a, b)
  }
}

trait semiring_modulo[A] extends comm_semiring_1_cancel[A] with modulo[A] {
}
object semiring_modulo {
  implicit def `Solver.semiring_modulo_nat`: semiring_modulo[nat] = new
    semiring_modulo[nat] {
    val `Solver.modulo` = (a: nat, b: nat) => modulo_nata(a, b)
    val `Solver.divide` = (a: nat, b: nat) => divide_nata(a, b)
    val `Solver.one` = one_nata
    val `Solver.times` = (a: nat, b: nat) => times_nata(a, b)
    val `Solver.zero` = zero_nata
    val `Solver.minus` = (a: nat, b: nat) => minus_nata(a, b)
    val `Solver.plus` = (a: nat, b: nat) => plus_nata(a, b)
  }
}

trait semidom_modulo[A] extends algebraic_semidom[A] with semiring_modulo[A] {
}
object semidom_modulo {
  implicit def `Solver.semidom_modulo_nat`: semidom_modulo[nat] = new
    semidom_modulo[nat] {
    val `Solver.modulo` = (a: nat, b: nat) => modulo_nata(a, b)
    val `Solver.divide` = (a: nat, b: nat) => divide_nata(a, b)
    val `Solver.minus` = (a: nat, b: nat) => minus_nata(a, b)
    val `Solver.one` = one_nata
    val `Solver.times` = (a: nat, b: nat) => times_nata(a, b)
    val `Solver.zero` = zero_nata
    val `Solver.plus` = (a: nat, b: nat) => plus_nata(a, b)
  }
}

def cEnum_nat:
      Option[(List[nat],
               ((nat => Boolean) => Boolean, (nat => Boolean) => Boolean))]
  =
  None

trait cenum[A] {
  val `Solver.cEnum`:
        Option[(List[A],
                 ((A => Boolean) => Boolean, (A => Boolean) => Boolean))]
}
def cEnum[A](implicit A: cenum[A]):
      Option[(List[A], ((A => Boolean) => Boolean, (A => Boolean) => Boolean))]
  = A.`Solver.cEnum`
object cenum {
  implicit def `Solver.cenum_nat`: cenum[nat] = new cenum[nat] {
    val `Solver.cEnum` = cEnum_nat
  }
}

abstract sealed class ordera
final case class Eq() extends ordera
final case class Lt() extends ordera
final case class Gt() extends ordera

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

def comparator_of[A : equal : linorder](x: A, y: A): ordera =
  (if (less[A](x, y)) Lt() else (if (eq[A](x, y)) Eq() else Gt()))

def compare_nat: nat => nat => ordera =
  ((a: nat) => (b: nat) => comparator_of[nat](a, b))

def ccompare_nata: Option[nat => nat => ordera] =
  Some[nat => nat => ordera](compare_nat)

trait ccompare[A] {
  val `Solver.ccompare`: Option[A => A => ordera]
}
def ccompare[A](implicit A: ccompare[A]): Option[A => A => ordera] =
  A.`Solver.ccompare`
object ccompare {
  implicit def
    `Solver.ccompare_prod`[A : ccompare, B : ccompare]: ccompare[(A, B)] = new
    ccompare[(A, B)] {
    val `Solver.ccompare` = ccompare_proda[A, B]
  }
  implicit def `Solver.ccompare_iarray`[A : ccompare]: ccompare[Array.T[A]] =
    new ccompare[Array.T[A]] {
    val `Solver.ccompare` = ccompare_iarraya[A]
  }
  implicit def `Solver.ccompare_nat`: ccompare[nat] = new ccompare[nat] {
    val `Solver.ccompare` = ccompare_nata
  }
}

def equal_boola(p: Boolean, pa: Boolean): Boolean = (p, pa) match {
  case (p, true) => p
  case (p, false) => ! p
  case (true, p) => p
  case (false, p) => ! p
}

def showsp_bool(p: nat, x1: Boolean): (List[char]) => List[char] = (p, x1) match
  {
  case (p, true) =>
    shows_string.apply(List(Char(false, false, true, false, true, false, true,
                                  false),
                             Char(false, true, false, false, true, true, true,
                                   false),
                             Char(true, false, true, false, true, true, true,
                                   false),
                             Char(true, false, true, false, false, true, true,
                                   false)))
  case (p, false) =>
    shows_string.apply(List(Char(false, true, true, false, false, false, true,
                                  false),
                             Char(true, false, false, false, false, true, true,
                                   false),
                             Char(false, false, true, true, false, true, true,
                                   false),
                             Char(true, true, false, false, true, true, true,
                                   false),
                             Char(true, false, true, false, false, true, true,
                                   false)))
}

def shows_prec_bool: nat => Boolean => (List[char]) => List[char] =
  ((a: nat) => (b: Boolean) => showsp_bool(a, b))

def shows_list_bool: (List[Boolean]) => (List[char]) => List[char] =
  ((a: List[Boolean]) => showsp_list[Boolean](shows_prec_bool, zero_nata, a))

def def_hashmap_size_bool: (itself[Boolean]) => nat =
  ((_: itself[Boolean]) => nat_of_integer(BigInt(2)))

def hashcode_bool(b: Boolean): Int = (if (b) 1 else 0)

def equal_lista[A : equal](x0: List[A], x1: List[A]): Boolean = (x0, x1) match {
  case (Nil, x21 :: x22) => false
  case (x21 :: x22, Nil) => false
  case (x21 :: x22, y21 :: y22) => eq[A](x21, y21) && equal_lista[A](x22, y22)
  case (Nil, Nil) => true
}

def def_hashmap_size_list[A : hashable]: (itself[List[A]]) => nat =
  ((_: itself[List[A]]) =>
    times_nata(nat_of_integer(BigInt(2)), def_hashmap_size[A](typea[A]())))

def foldl[A, B](f: A => B => A, a: A, x2: List[B]): A = (f, a, x2) match {
  case (f, a, Nil) => a
  case (f, a, x :: xs) => foldl[A, B](f, (f(a))(x), xs)
}

def hashcode_list[A : hashable]: (List[A]) => Int =
  ((a: List[A]) =>
    foldl[Int, A](((h: Int) => (x: A) =>
                    h * BigInt(33).intValue + hashcode[A](x)),
                   BigInt(5381).intValue, a))

def uminus_int(k: int): int = int_of_integer((- (integer_of_int(k))))

def zero_int: int = int_of_integer(BigInt(0))

def less_int(k: int, l: int): Boolean = integer_of_int(k) < integer_of_int(l)

def nat(k: int): nat = Nat(max[BigInt](BigInt(0), integer_of_int(k)))

def showsp_int(p: nat, i: int): (List[char]) => List[char] =
  (if (less_int(i, zero_int))
    comp[List[char], List[char],
          List[char]](shows_string.apply(List(Char(true, false, true, true,
            false, true, false, false))),
                       showsp_nat(p, nat(uminus_int(i))))
    else showsp_nat(p, nat(i)))

def one_int: int = int_of_integer(BigInt(1))

abstract sealed class rat
final case class Frct(a: (int, int)) extends rat

def quotient_of(x0: rat): (int, int) = x0 match {
  case Frct(x) => x
}

def showsp_rat(p: nat, x: rat): (List[char]) => List[char] =
  {
    val (d, n) = quotient_of(x): ((int, int));
    (if (equal_inta(n, one_int)) showsp_int(p, d)
      else comp[List[char], List[char],
                 List[char]](comp[List[char], List[char],
                                   List[char]](showsp_int(p, d),
        shows_string.apply(List(Char(true, true, true, true, false, true, false,
                                      false)))),
                              showsp_int(p, n)))
  }

def shows_prec_rat: nat => rat => (List[char]) => List[char] =
  ((a: nat) => (b: rat) => showsp_rat(a, b))

abstract sealed class real
final case class Ratreal(a: rat) extends real

def show_reala(x0: real): List[char] = x0 match {
  case Ratreal(x) => shows_prec_rat.apply(zero_nata).apply(x).apply(Nil)
}

def showsp_real(p: nat, x: real, y: List[char]): List[char] = show_reala(x) ++ y

def shows_prec_real: nat => real => (List[char]) => List[char] =
  ((a: nat) => (b: real) => (c: List[char]) => showsp_real(a, b, c))

def shows_list_real: (List[real]) => (List[char]) => List[char] =
  ((a: List[real]) => showsp_list[real](shows_prec_real, zero_nata, a))

def one_rat: rat = Frct((one_int, one_int))

def one_reala: real = Ratreal(one_rat)

def times_int(k: int, l: int): int =
  int_of_integer(integer_of_int(k) * integer_of_int(l))

def plus_int(k: int, l: int): int =
  int_of_integer(integer_of_int(k) + integer_of_int(l))

def divide_int(k: int, l: int): int =
  int_of_integer(divide_integer(integer_of_int(k), integer_of_int(l)))

def gcd_int(x0: int, x1: int): int = (x0, x1) match {
  case (int_of_integer(x), int_of_integer(y)) => int_of_integer(x.gcd(y))
}

def normalize(p: (int, int)): (int, int) =
  (if (less_int(zero_int, snd[int, int](p)))
    {
      val a = gcd_int(fst[int, int](p), snd[int, int](p)): int;
      (divide_int(fst[int, int](p), a), divide_int(snd[int, int](p), a))
    }
    else (if (equal_inta(snd[int, int](p), zero_int)) (zero_int, one_int)
           else {
                  val a =
                    uminus_int(gcd_int(fst[int, int](p), snd[int, int](p))):
                      int;
                  (divide_int(fst[int, int](p), a),
                    divide_int(snd[int, int](p), a))
                }))

def plus_rat(p: rat, q: rat): rat =
  Frct({
         val (a, c) = quotient_of(p): ((int, int))
         val (b, d) = quotient_of(q): ((int, int));
         normalize((plus_int(times_int(a, d), times_int(b, c)),
                     times_int(c, d)))
       })

def plus_reala(x0: real, x1: real): real = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Ratreal(plus_rat(x, y))
}

def zero_rat: rat = Frct((zero_int, one_int))

def zero_reala: real = Ratreal(zero_rat)

def times_rat(p: rat, q: rat): rat =
  Frct({
         val (a, c) = quotient_of(p): ((int, int))
         val (b, d) = quotient_of(q): ((int, int));
         normalize((times_int(a, b), times_int(c, d)))
       })

def times_reala(x0: real, x1: real): real = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Ratreal(times_rat(x, y))
}

def minus_int(k: int, l: int): int =
  int_of_integer(integer_of_int(k) - integer_of_int(l))

def minus_rat(p: rat, q: rat): rat =
  Frct({
         val (a, c) = quotient_of(p): ((int, int))
         val (b, d) = quotient_of(q): ((int, int));
         normalize((minus_int(times_int(a, d), times_int(b, c)),
                     times_int(c, d)))
       })

def minus_reala(x0: real, x1: real): real = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Ratreal(minus_rat(x, y))
}

def uminus_rat(p: rat): rat = Frct({
                                     val (a, b) = quotient_of(p): ((int, int));
                                     (uminus_int(a), b)
                                   })

def uminus_reala(x0: real): real = x0 match {
  case Ratreal(x) => Ratreal(uminus_rat(x))
}

trait uminus[A] {
  val `Solver.uminus`: A => A
}
def uminus[A](a: A)(implicit A: uminus[A]): A = A.`Solver.uminus`(a)
object uminus {
  implicit def `Solver.uminus_real`: uminus[real] = new uminus[real] {
    val `Solver.uminus` = (a: real) => uminus_reala(a)
  }
}

def less_eq_int(k: int, l: int): Boolean =
  integer_of_int(k) <= integer_of_int(l)

def less_eq_rat(p: rat, q: rat): Boolean =
  {
    val (a, c) = quotient_of(p): ((int, int))
    val (b, d) = quotient_of(q): ((int, int));
    less_eq_int(times_int(a, d), times_int(c, b))
  }

def less_eq_real(x0: real, x1: real): Boolean = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => less_eq_rat(x, y)
}

def less_rat(p: rat, q: rat): Boolean =
  {
    val (a, c) = quotient_of(p): ((int, int))
    val (b, d) = quotient_of(q): ((int, int));
    less_int(times_int(a, d), times_int(c, b))
  }

def less_real(x0: real, x1: real): Boolean = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => less_rat(x, y)
}

def map[A, B](f: A => B, x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x21 :: x22) => f(x21) :: map[A, B](f, x22)
}

def length[A](as: Array.T[A]): nat = nat_of_integer(Array.len[A](as))

def sub[A](as: Array.T[A], n: nat): A =
  (as, integer_of_nat(n)) match { case (a,b) => Array.nth(a,b) }

def upt_aux(i: nat, j: nat, acc: List[nat]): List[nat] =
  (if (less_eq_nat(j, i)) acc else {
                                     val ja = minus_nata(j, one_nata): nat;
                                     upt_aux(i, ja, ja :: acc)
                                   })

def upt_tr(i: nat, j: nat): List[nat] = upt_aux(i, j, Nil)

def upt: nat => nat => List[nat] = ((a: nat) => (b: nat) => upt_tr(a, b))

def list_of[A](as: Array.T[A]): List[A] =
  map[nat, A](((a: nat) => sub[A](as, a)),
               upt.apply(zero_nata).apply(length[A](as)))

def equal_iarray[A : equal](as: Array.T[A], bs: Array.T[A]): Boolean =
  equal_lista[A](list_of[A](as), list_of[A](bs))

def ceq_iarraya[A : ceq : equal]:
      Option[(Array.T[A]) => (Array.T[A]) => Boolean]
  =
  Some[(Array.T[A]) =>
         (Array.T[A]) =>
           Boolean](((a: Array.T[A]) => (b: Array.T[A]) =>
                      equal_iarray[A](a, b)))

def set_impl_iarraya[A]: phantom[Array.T[A], set_impla] =
  phantoma[set_impla, Array.T[A]](set_DList())

def ccompare_iarraya[A : ccompare]:
      Option[(Array.T[A]) => (Array.T[A]) => ordera]
  =
  None

def equal_optiona[A : equal](x0: Option[A], x1: Option[A]): Boolean = (x0, x1)
  match {
  case (None, Some(x2)) => false
  case (Some(x2), None) => false
  case (Some(x2), Some(y2)) => eq[A](x2, y2)
  case (None, None) => true
}

def def_hashmap_size_option[A : hashable]: (itself[Option[A]]) => nat =
  ((_: itself[Option[A]]) =>
    plus_nata(def_hashmap_size[A](typea[A]()), one_nata))

def hashcode_option[A : hashable](opt: Option[A]): Int =
  (opt match {
     case None => 0
     case Some(a) => hashcode[A](a) + 1
   })

def equal_proda[A : equal, B : equal](x0: (A, B), x1: (A, B)): Boolean =
  (x0, x1) match {
  case ((x1, x2), (y1, y2)) => eq[A](x1, y1) && eq[B](x2, y2)
}

def equality_prod[A, B](eq_a: A => A => Boolean, eq_b: B => B => Boolean,
                         x2: (A, B), x3: (A, B)):
      Boolean
  =
  (eq_a, eq_b, x2, x3) match {
  case (eq_a, eq_b, (x, xa), (y, ya)) => (eq_a(x))(y) && (eq_b(xa))(ya)
}

def ceq_proda[A : ceq, B : ceq]: Option[((A, B)) => ((A, B)) => Boolean] =
  (ceq[A] match {
     case None => None
     case Some(eq_a) =>
       (ceq[B] match {
          case None => None
          case Some(eq_b) =>
            Some[((A, B)) =>
                   ((A, B)) =>
                     Boolean](((a: (A, B)) => (b: (A, B)) =>
                                equality_prod[A, B](eq_a, eq_b, a, b)))
        })
   })

def def_hashmap_size_prod[A : hashable, B : hashable]: (itself[(A, B)]) => nat =
  ((_: itself[(A, B)]) =>
    plus_nata(def_hashmap_size[A](typea[A]()), def_hashmap_size[B](typea[B]())))

def hashcode_prod[A : hashable, B : hashable](x: (A, B)): Int =
  hashcode[A](fst[A, B](x)) * BigInt(33).intValue + hashcode[B](snd[A, B](x))

def comparator_prod[A, B](comp_a: A => A => ordera, comp_b: B => B => ordera,
                           x2: (A, B), x3: (A, B)):
      ordera
  =
  (comp_a, comp_b, x2, x3) match {
  case (comp_a, comp_b, (x, xa), (y, ya)) => ((comp_a(x))(y) match {
        case Eq() => (comp_b(xa))(ya)
        case Lt() => Lt()
        case Gt() => Gt()
      })
}

def ccompare_proda[A : ccompare, B : ccompare]:
      Option[((A, B)) => ((A, B)) => ordera]
  =
  (ccompare[A] match {
     case None => None
     case Some(comp_a) =>
       (ccompare[B] match {
          case None => None
          case Some(comp_b) =>
            Some[((A, B)) =>
                   ((A, B)) =>
                     ordera](((a: (A, B)) => (b: (A, B)) =>
                               comparator_prod[A, B](comp_a, comp_b, a, b)))
        })
   })

def equal_unita(u: Unit, v: Unit): Boolean = true

abstract sealed class ereal
final case class ereala(a: real) extends ereal
final case class PInfty() extends ereal
final case class MInfty() extends ereal

def plus_ereala(a: ereal, aa: ereal): ereal = (a, aa) match {
  case (ereala(r), ereala(p)) => ereala(plus_reala(r, p))
  case (PInfty(), a) => PInfty()
  case (a, PInfty()) => PInfty()
  case (ereala(r), MInfty()) => MInfty()
  case (MInfty(), ereala(p)) => MInfty()
  case (MInfty(), MInfty()) => MInfty()
}

def zero_ereala: ereal = ereala(zero_reala)

def equal_rat(a: rat, b: rat): Boolean =
  equal_proda[int, int](quotient_of(a), quotient_of(b))

def equal_real(x0: real, x1: real): Boolean = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => equal_rat(x, y)
}

def equal_ereal(x0: ereal, x1: ereal): Boolean = (x0, x1) match {
  case (PInfty(), MInfty()) => false
  case (MInfty(), PInfty()) => false
  case (ereala(x1), MInfty()) => false
  case (MInfty(), ereala(x1)) => false
  case (ereala(x1), PInfty()) => false
  case (PInfty(), ereala(x1)) => false
  case (ereala(x1), ereala(y1)) => equal_real(x1, y1)
  case (MInfty(), MInfty()) => true
  case (PInfty(), PInfty()) => true
}

def less_ereal(a: ereal, aa: ereal): Boolean = (a, aa) match {
  case (ereala(x), ereala(y)) => less_real(x, y)
  case (PInfty(), a) => false
  case (a, MInfty()) => false
  case (ereala(x), PInfty()) => true
  case (MInfty(), ereala(r)) => true
  case (MInfty(), PInfty()) => true
}

def less_eq_ereal(x: ereal, y: ereal): Boolean =
  less_ereal(x, y) || equal_ereal(x, y)

def one_integera: BigInt = BigInt(1)

abstract sealed class f_name_code
final case class f_c_code(a: nat) extends f_name_code
final case class f_b_code(a: nat) extends f_name_code
final case class f_e_code(a: nat) extends f_name_code

def equal_f_name_code(x0: f_name_code, x1: f_name_code): Boolean = (x0, x1)
  match {
  case (f_b_code(x2), f_e_code(x3)) => false
  case (f_e_code(x3), f_b_code(x2)) => false
  case (f_c_code(x1), f_e_code(x3)) => false
  case (f_e_code(x3), f_c_code(x1)) => false
  case (f_c_code(x1), f_b_code(x2)) => false
  case (f_b_code(x2), f_c_code(x1)) => false
  case (f_e_code(x3), f_e_code(y3)) => equal_nata(x3, y3)
  case (f_b_code(x2), f_b_code(y2)) => equal_nata(x2, y2)
  case (f_c_code(x1), f_c_code(y1)) => equal_nata(x1, y1)
}

abstract sealed class var_code[A, B]
final case class var_phi[A, B]() extends var_code[A, B]
final case class var_f[A, B](a: A, b: f_name_code, c: B) extends var_code[A, B]
final case class var_w[A, B](a: nat) extends var_code[A, B]

def equal_var_codea[A : equal,
                     B : equal](x0: var_code[A, B], x1: var_code[A, B]):
      Boolean
  =
  (x0, x1) match {
  case (var_f(x21, x22, x23), var_w(x3)) => false
  case (var_w(x3), var_f(x21, x22, x23)) => false
  case (var_phi(), var_w(x3)) => false
  case (var_w(x3), var_phi()) => false
  case (var_phi(), var_f(x21, x22, x23)) => false
  case (var_f(x21, x22, x23), var_phi()) => false
  case (var_w(x3), var_w(y3)) => equal_nata(x3, y3)
  case (var_f(x21, x22, x23), var_f(y21, y22, y23)) =>
    eq[A](x21, y21) && (equal_f_name_code(x22, y22) && eq[B](x23, y23))
  case (var_phi(), var_phi()) => true
}

def def_hashmap_size_var_code[A : hashable, B : hashable]:
      (itself[var_code[A, B]]) => nat
  =
  ((_: itself[var_code[A, B]]) => nat_of_integer(BigInt(10)))

def hash_code_f_name_code(x0: f_name_code): Int = x0 match {
  case f_e_code(x) =>
    hashcode_nat(x) * BigInt(330724615).intValue + BigInt(228131704).intValue
  case f_b_code(x) =>
    hashcode_nat(x) * BigInt(2084995094).intValue + BigInt(1982402183).intValue
  case f_c_code(x) =>
    hashcode_nat(x) * BigInt(784410385).intValue + BigInt(681817474).intValue
}

def hash_code_var_code[A, B](h_x: A => Int, h_v: B => Int, x2: var_code[A, B]):
      Int
  =
  (h_x, h_v, x2) match {
  case (h_x, h_v, var_w(x)) =>
    hashcode_nat(x) * BigInt(2088942312).intValue + BigInt(1986349401).intValue
  case (h_x, h_v, var_f(x, xa, xb)) =>
    h_x(x) * BigInt(838851669).intValue +
      (hash_code_f_name_code(xa) * BigInt(736258758).intValue +
        (h_v(xb) * BigInt(633665847).intValue + BigInt(531072936).intValue))
  case (h_x, h_v, var_phi()) => BigInt(386317318).intValue
}

def hashcode_var_code[A : hashable, B : hashable]: (var_code[A, B]) => Int =
  ((a: var_code[A, B]) =>
    hash_code_var_code[A, B](((aa: A) => hashcode[A](aa)),
                              ((aa: B) => hashcode[B](aa)), a))

abstract sealed class color
final case class R() extends color
final case class B() extends color

abstract sealed class rbta[A, B]
final case class Empty[A, B]() extends rbta[A, B]
final case class Branch[A, B](a: color, b: rbta[A, B], c: A, d: B,
                               e: rbta[A, B])
  extends rbta[A, B]

abstract sealed class rbt[B, A]
final case class RBT[B, A](a: rbta[B, A]) extends rbt[B, A]

abstract sealed class mapping_rbt[B, A]
final case class Mapping_RBT[B, A](a: rbta[B, A]) extends mapping_rbt[B, A]

abstract sealed class set_dlist[A]
final case class Abs_dlist[A](a: List[A]) extends set_dlist[A]

abstract sealed class set[A]
final case class Collect_set[A](a: A => Boolean) extends set[A]
final case class DList_set[A](a: set_dlist[A]) extends set[A]
final case class RBT_set[A](a: mapping_rbt[A, Unit]) extends set[A]
final case class Set_Monad[A](a: List[A]) extends set[A]
final case class Complement[A](a: set[A]) extends set[A]

abstract sealed class tree[A]
final case class Leaf[A]() extends tree[A]
final case class Node[A](a: tree[A], b: A, c: tree[A]) extends tree[A]

abstract sealed class LP_Cert[A]
final case class Cert_Opt[A](a: A, b: A) extends LP_Cert[A]
final case class Cert_Infeas[A](a: A) extends LP_Cert[A]
final case class Cert_Unbounded[A](a: A, b: A) extends LP_Cert[A]

abstract sealed class mapping[A, B]
final case class Mapping[A, B](a: rbt[A, B]) extends mapping[A, B]

abstract sealed class rat_pair
final case class Abs_rat_pair(a: (int, int)) extends rat_pair

abstract sealed class real_code
final case class Frcta(a: rat_pair) extends real_code

abstract sealed class hashmapa[A, B]
final case class HashMapa[A, B](a: DiffArray.T[(List[(A, B)])], b: nat) extends
  hashmapa[A, B]

abstract sealed class hashmap[B, A]
final case class HashMap[B, A](a: hashmapa[B, A]) extends hashmap[B, A]

abstract sealed class generator[A, B]
final case class Generator[B, A](a: (B => Boolean, B => (A, B))) extends
  generator[A, B]

abstract sealed class lp_res[A]
final case class Opt[A](a: A, b: real) extends lp_res[A]
final case class Infeasible[A]() extends lp_res[A]
final case class Unbounded[A]() extends lp_res[A]

abstract sealed class Constr_Code[A]
final case class Constr_Le[A](a: A, b: real) extends Constr_Code[A]
final case class Constr_Eq[A](a: A, b: real) extends Constr_Code[A]

abstract sealed class LP_Code[A]
final case class LP_Codea[A](a: A, b: List[Constr_Code[A]]) extends LP_Code[A]

abstract sealed class Scoped_Tree[A]
final case class Scoped_Leaf[A](a: A) extends Scoped_Tree[A]
final case class Scoped_Node[A](a: nat, b: Array.T[(Scoped_Tree[A])]) extends
  Scoped_Tree[A]

abstract sealed class bound[A]
final case class Lb[A](a: A, b: Option[real]) extends bound[A]
final case class Ub[A](a: A, b: Option[real]) extends bound[A]
final case class Betw[A](a: Option[real], b: A, c: Option[real]) extends
  bound[A]
final case class Beq[A](a: A, b: real) extends bound[A]
final case class Free[A](a: A) extends bound[A]

abstract sealed class sense
final case class Leq() extends sense
final case class Geq() extends sense
final case class Eqa() extends sense

abstract sealed class pmf[A]
final case class pmf_of_mapping[A](a: mapping[A, real]) extends pmf[A]

abstract sealed class pmf_ops_ext[A, B, C, D]
final case class pmf_ops_exta[A, B, C,
                               D](a: A => pmf[B], b: A => B => real, c: A => C,
                                   d: A => Boolean, e: D)
  extends pmf_ops_ext[A, B, C, D]

abstract sealed class vec_ops_ext[A, B, C, D]
final case class vec_ops_exta[A, B, C,
                               D](a: A => nat => Option[B], b: A => C,
                                   c: A => nat => B, d: A => Boolean, e: A,
                                   f: A => nat => B => A, g: A => C => A, h: D)
  extends vec_ops_ext[A, B, C, D]

abstract sealed class api_input_ext[A, B, C]
final case class api_input_exta[A, B,
                                 C](a: nat, b: nat => nat, c: nat, d: real,
                                     e: nat => nat => Scoped_Tree[real],
                                     f: nat => nat => A, g: nat => nat, h: nat,
                                     i: nat, j: nat => nat => Scoped_Tree[B],
                                     k: nat => nat => A, l: real,
                                     m: nat => Scoped_Tree[real], n: nat => A,
                                     o: nat, p: nat => A, q: C)
  extends api_input_ext[A, B, C]

abstract sealed class scoped_fn_real_ops_ext[A, B]
final case class scoped_fn_real_ops_exta[A,
  B](a: A => real => A, b: A => A => A, c: B)
  extends scoped_fn_real_ops_ext[A, B]

abstract sealed class scoped_fn_ereal_ops_ext[A, B, C]
final case class scoped_fn_ereal_ops_exta[B, A, C](a: B => A, b: C) extends
  scoped_fn_ereal_ops_ext[A, B, C]

abstract sealed class scoped_fn_basic_ops_ext[A, B, C, D, E]
final case class scoped_fn_basic_ops_exta[A, B, C, D,
   E](a: A => B => C, b: A => set[nat], c: A => D, d: D => (B => C) => A,
       e: A => Boolean, f: A => B => A, g: A => A, h: E)
  extends scoped_fn_basic_ops_ext[A, B, C, D, E]

def id[A]: A => A = ((x: A) => x)

def Suc(n: nat): nat = plus_nata(n, one_nata)

def nth[A](x0: List[A], n: nat): A = (x0, n) match {
  case (x :: xs, n) =>
    (if (equal_nata(n, zero_nata)) x else nth[A](xs, minus_nata(n, one_nata)))
}

def fold[A, B](f: A => B => B, x1: List[A], s: B): B = (f, x1, s) match {
  case (f, x :: xs, s) => fold[A, B](f, xs, (f(x))(s))
  case (f, Nil, s) => s
}

def rev[A](xs: List[A]): List[A] =
  fold[A, List[A]](((a: A) => (b: List[A]) => a :: b), xs, Nil)

def list_of_dlist[A : ceq](x0: set_dlist[A]): List[A] = x0 match {
  case Abs_dlist(x) => x
}

def list_all[A](p: A => Boolean, x1: List[A]): Boolean = (p, x1) match {
  case (p, Nil) => true
  case (p, x :: xs) => p(x) && list_all[A](p, xs)
}

def dlist_all[A : ceq](x: A => Boolean, xc: set_dlist[A]): Boolean =
  list_all[A](x, list_of_dlist[A](xc))

def impl_ofa[B : ccompare, A](x0: mapping_rbt[B, A]): rbta[B, A] = x0 match {
  case Mapping_RBT(x) => x
}

def RBT_Impl_rbt_all[A, B](p: A => B => Boolean, x1: rbta[A, B]): Boolean =
  (p, x1) match {
  case (p, Branch(c, l, k, v, r)) =>
    (p(k))(v) && (RBT_Impl_rbt_all[A, B](p, l) && RBT_Impl_rbt_all[A, B](p, r))
  case (p, Empty()) => true
}

def all[A : ccompare, B](xb: A => B => Boolean, xc: mapping_rbt[A, B]): Boolean
  =
  RBT_Impl_rbt_all[A, B](xb, impl_ofa[A, B](xc))

def Ball[A : ceq : ccompare](x0: set[A], p: A => Boolean): Boolean = (x0, p)
  match {
  case (RBT_set(rbt), p) =>
    (ccompare[A] match {
       case None =>
         { sys.error("Ball RBT_set: ccompare = None");
           (((_: Unit) => Ball[A](RBT_set[A](rbt), p))).apply(()) }
       case Some(_) => all[A, Unit](((k: A) => (_: Unit) => p(k)), rbt)
     })
  case (DList_set(dxs), p) =>
    (ceq[A] match {
       case None =>
         { sys.error("Ball DList_set: ceq = None");
           (((_: Unit) => Ball[A](DList_set[A](dxs), p))).apply(()) }
       case Some(_) => dlist_all[A](p, dxs)
     })
  case (Set_Monad(xs), p) => list_all[A](p, xs)
}

def maps[A, B](f: A => List[B], x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) => f(x) ++ maps[A, B](f, xs)
}

def Fract(a: int, b: int): rat = Frct(normalize((a, b)))

def foldr[A, B](f: A => B => B, x1: List[A]): B => B = (f, x1) match {
  case (f, Nil) => id[B]
  case (f, x :: xs) => comp[B, B, B](f(x), foldr[A, B](f, xs))
}

def map_of[A : equal, B](x0: List[(A, B)], k: A): Option[B] = (x0, k) match {
  case ((l, v) :: ps, k) =>
    (if (eq[A](l, k)) Some[B](v) else map_of[A, B](ps, k))
  case (Nil, k) => None
}

def funpow[A](n: nat, f: A => A): A => A =
  (if (equal_nata(n, zero_nata)) id[A]
    else comp[A, A, A](f, funpow[A](minus_nata(n, one_nata), f)))

def of_int(a: int): rat = Frct((a, one_int))

def fun_upd[A, B](equal: A => A => Boolean, f: A => B, aa: A, b: B, a: A): B =
  (if ((equal(aa))(a)) b else f(a))

def balance[A, B](x0: rbta[A, B], s: A, t: B, x3: rbta[A, B]): rbta[A, B] =
  (x0, s, t, x3) match {
  case (Branch(R(), a, w, x, b), s, t, Branch(R(), c, y, z, d)) =>
    Branch[A, B](R(), Branch[A, B](B(), a, w, x, b), s, t,
                  Branch[A, B](B(), c, y, z, d))
  case (Branch(R(), Branch(R(), a, w, x, b), s, t, c), y, z, Empty()) =>
    Branch[A, B](R(), Branch[A, B](B(), a, w, x, b), s, t,
                  Branch[A, B](B(), c, y, z, Empty[A, B]()))
  case (Branch(R(), Branch(R(), a, w, x, b), s, t, c), y, z,
         Branch(B(), va, vb, vc, vd))
    => Branch[A, B](R(), Branch[A, B](B(), a, w, x, b), s, t,
                     Branch[A, B](B(), c, y, z,
                                   Branch[A, B](B(), va, vb, vc, vd)))
  case (Branch(R(), Empty(), w, x, Branch(R(), b, s, t, c)), y, z, Empty()) =>
    Branch[A, B](R(), Branch[A, B](B(), Empty[A, B](), w, x, b), s, t,
                  Branch[A, B](B(), c, y, z, Empty[A, B]()))
  case (Branch(R(), Branch(B(), va, vb, vc, vd), w, x, Branch(R(), b, s, t, c)),
         y, z, Empty())
    => Branch[A, B](R(), Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), w,
                                       x, b),
                     s, t, Branch[A, B](B(), c, y, z, Empty[A, B]()))
  case (Branch(R(), Empty(), w, x, Branch(R(), b, s, t, c)), y, z,
         Branch(B(), va, vb, vc, vd))
    => Branch[A, B](R(), Branch[A, B](B(), Empty[A, B](), w, x, b), s, t,
                     Branch[A, B](B(), c, y, z,
                                   Branch[A, B](B(), va, vb, vc, vd)))
  case (Branch(R(), Branch(B(), ve, vf, vg, vh), w, x, Branch(R(), b, s, t, c)),
         y, z, Branch(B(), va, vb, vc, vd))
    => Branch[A, B](R(), Branch[A, B](B(), Branch[A, B](B(), ve, vf, vg, vh), w,
                                       x, b),
                     s, t,
                     Branch[A, B](B(), c, y, z,
                                   Branch[A, B](B(), va, vb, vc, vd)))
  case (Empty(), w, x, Branch(R(), b, s, t, Branch(R(), c, y, z, d))) =>
    Branch[A, B](R(), Branch[A, B](B(), Empty[A, B](), w, x, b), s, t,
                  Branch[A, B](B(), c, y, z, d))
  case (Branch(B(), va, vb, vc, vd), w, x,
         Branch(R(), b, s, t, Branch(R(), c, y, z, d)))
    => Branch[A, B](R(), Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), w,
                                       x, b),
                     s, t, Branch[A, B](B(), c, y, z, d))
  case (Empty(), w, x, Branch(R(), Branch(R(), b, s, t, c), y, z, Empty())) =>
    Branch[A, B](R(), Branch[A, B](B(), Empty[A, B](), w, x, b), s, t,
                  Branch[A, B](B(), c, y, z, Empty[A, B]()))
  case (Empty(), w, x,
         Branch(R(), Branch(R(), b, s, t, c), y, z,
                 Branch(B(), va, vb, vc, vd)))
    => Branch[A, B](R(), Branch[A, B](B(), Empty[A, B](), w, x, b), s, t,
                     Branch[A, B](B(), c, y, z,
                                   Branch[A, B](B(), va, vb, vc, vd)))
  case (Branch(B(), va, vb, vc, vd), w, x,
         Branch(R(), Branch(R(), b, s, t, c), y, z, Empty()))
    => Branch[A, B](R(), Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), w,
                                       x, b),
                     s, t, Branch[A, B](B(), c, y, z, Empty[A, B]()))
  case (Branch(B(), va, vb, vc, vd), w, x,
         Branch(R(), Branch(R(), b, s, t, c), y, z,
                 Branch(B(), ve, vf, vg, vh)))
    => Branch[A, B](R(), Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), w,
                                       x, b),
                     s, t,
                     Branch[A, B](B(), c, y, z,
                                   Branch[A, B](B(), ve, vf, vg, vh)))
  case (Empty(), s, t, Empty()) =>
    Branch[A, B](B(), Empty[A, B](), s, t, Empty[A, B]())
  case (Empty(), s, t, Branch(B(), va, vb, vc, vd)) =>
    Branch[A, B](B(), Empty[A, B](), s, t, Branch[A, B](B(), va, vb, vc, vd))
  case (Empty(), s, t, Branch(v, Empty(), vb, vc, Empty())) =>
    Branch[A, B](B(), Empty[A, B](), s, t,
                  Branch[A, B](v, Empty[A, B](), vb, vc, Empty[A, B]()))
  case (Empty(), s, t, Branch(v, Branch(B(), ve, vf, vg, vh), vb, vc, Empty()))
    => Branch[A, B](B(), Empty[A, B](), s, t,
                     Branch[A, B](v, Branch[A, B](B(), ve, vf, vg, vh), vb, vc,
                                   Empty[A, B]()))
  case (Empty(), s, t, Branch(v, Empty(), vb, vc, Branch(B(), vf, vg, vh, vi)))
    => Branch[A, B](B(), Empty[A, B](), s, t,
                     Branch[A, B](v, Empty[A, B](), vb, vc,
                                   Branch[A, B](B(), vf, vg, vh, vi)))
  case (Empty(), s, t,
         Branch(v, Branch(B(), ve, vj, vk, vl), vb, vc,
                 Branch(B(), vf, vg, vh, vi)))
    => Branch[A, B](B(), Empty[A, B](), s, t,
                     Branch[A, B](v, Branch[A, B](B(), ve, vj, vk, vl), vb, vc,
                                   Branch[A, B](B(), vf, vg, vh, vi)))
  case (Branch(B(), va, vb, vc, vd), s, t, Empty()) =>
    Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), s, t, Empty[A, B]())
  case (Branch(B(), va, vb, vc, vd), s, t, Branch(B(), ve, vf, vg, vh)) =>
    Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), s, t,
                  Branch[A, B](B(), ve, vf, vg, vh))
  case (Branch(B(), va, vb, vc, vd), s, t, Branch(v, Empty(), vf, vg, Empty()))
    => Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), s, t,
                     Branch[A, B](v, Empty[A, B](), vf, vg, Empty[A, B]()))
  case (Branch(B(), va, vb, vc, vd), s, t,
         Branch(v, Branch(B(), vi, vj, vk, vl), vf, vg, Empty()))
    => Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), s, t,
                     Branch[A, B](v, Branch[A, B](B(), vi, vj, vk, vl), vf, vg,
                                   Empty[A, B]()))
  case (Branch(B(), va, vb, vc, vd), s, t,
         Branch(v, Empty(), vf, vg, Branch(B(), vj, vk, vl, vm)))
    => Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), s, t,
                     Branch[A, B](v, Empty[A, B](), vf, vg,
                                   Branch[A, B](B(), vj, vk, vl, vm)))
  case (Branch(B(), va, vb, vc, vd), s, t,
         Branch(v, Branch(B(), vi, vn, vo, vp), vf, vg,
                 Branch(B(), vj, vk, vl, vm)))
    => Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), s, t,
                     Branch[A, B](v, Branch[A, B](B(), vi, vn, vo, vp), vf, vg,
                                   Branch[A, B](B(), vj, vk, vl, vm)))
  case (Branch(v, Empty(), vb, vc, Empty()), s, t, Empty()) =>
    Branch[A, B](B(), Branch[A, B](v, Empty[A, B](), vb, vc, Empty[A, B]()), s,
                  t, Empty[A, B]())
  case (Branch(v, Empty(), vb, vc, Branch(B(), ve, vf, vg, vh)), s, t, Empty())
    => Branch[A, B](B(), Branch[A, B](v, Empty[A, B](), vb, vc,
                                       Branch[A, B](B(), ve, vf, vg, vh)),
                     s, t, Empty[A, B]())
  case (Branch(v, Branch(B(), vf, vg, vh, vi), vb, vc, Empty()), s, t, Empty())
    => Branch[A, B](B(), Branch[A, B](v, Branch[A, B](B(), vf, vg, vh, vi), vb,
                                       vc, Empty[A, B]()),
                     s, t, Empty[A, B]())
  case (Branch(v, Branch(B(), vf, vg, vh, vi), vb, vc,
                Branch(B(), ve, vj, vk, vl)),
         s, t, Empty())
    => Branch[A, B](B(), Branch[A, B](v, Branch[A, B](B(), vf, vg, vh, vi), vb,
                                       vc, Branch[A, B](B(), ve, vj, vk, vl)),
                     s, t, Empty[A, B]())
  case (Branch(v, Empty(), vf, vg, Empty()), s, t, Branch(B(), va, vb, vc, vd))
    => Branch[A, B](B(), Branch[A, B](v, Empty[A, B](), vf, vg, Empty[A, B]()),
                     s, t, Branch[A, B](B(), va, vb, vc, vd))
  case (Branch(v, Empty(), vf, vg, Branch(B(), vi, vj, vk, vl)), s, t,
         Branch(B(), va, vb, vc, vd))
    => Branch[A, B](B(), Branch[A, B](v, Empty[A, B](), vf, vg,
                                       Branch[A, B](B(), vi, vj, vk, vl)),
                     s, t, Branch[A, B](B(), va, vb, vc, vd))
  case (Branch(v, Branch(B(), vj, vk, vl, vm), vf, vg, Empty()), s, t,
         Branch(B(), va, vb, vc, vd))
    => Branch[A, B](B(), Branch[A, B](v, Branch[A, B](B(), vj, vk, vl, vm), vf,
                                       vg, Empty[A, B]()),
                     s, t, Branch[A, B](B(), va, vb, vc, vd))
  case (Branch(v, Branch(B(), vj, vk, vl, vm), vf, vg,
                Branch(B(), vi, vn, vo, vp)),
         s, t, Branch(B(), va, vb, vc, vd))
    => Branch[A, B](B(), Branch[A, B](v, Branch[A, B](B(), vj, vk, vl, vm), vf,
                                       vg, Branch[A, B](B(), vi, vn, vo, vp)),
                     s, t, Branch[A, B](B(), va, vb, vc, vd))
}

def rbt_comp_ins[A, B](c: A => A => ordera, f: A => B => B => B, k: A, v: B,
                        x4: rbta[A, B]):
      rbta[A, B]
  =
  (c, f, k, v, x4) match {
  case (c, f, k, v, Empty()) =>
    Branch[A, B](R(), Empty[A, B](), k, v, Empty[A, B]())
  case (c, f, k, v, Branch(B(), l, x, y, r)) =>
    ((c(k))(x) match {
       case Eq() => Branch[A, B](B(), l, x, ((f(k))(y))(v), r)
       case Lt() => balance[A, B](rbt_comp_ins[A, B](c, f, k, v, l), x, y, r)
       case Gt() => balance[A, B](l, x, y, rbt_comp_ins[A, B](c, f, k, v, r))
     })
  case (c, f, k, v, Branch(R(), l, x, y, r)) =>
    ((c(k))(x) match {
       case Eq() => Branch[A, B](R(), l, x, ((f(k))(y))(v), r)
       case Lt() =>
         Branch[A, B](R(), rbt_comp_ins[A, B](c, f, k, v, l), x, y, r)
       case Gt() =>
         Branch[A, B](R(), l, x, y, rbt_comp_ins[A, B](c, f, k, v, r))
     })
}

def paint[A, B](c: color, x1: rbta[A, B]): rbta[A, B] = (c, x1) match {
  case (c, Empty()) => Empty[A, B]()
  case (c, Branch(uu, l, k, v, r)) => Branch[A, B](c, l, k, v, r)
}

def rbt_comp_insert_with_key[A, B](c: A => A => ordera, f: A => B => B => B,
                                    k: A, v: B, t: rbta[A, B]):
      rbta[A, B]
  =
  paint[A, B](B(), rbt_comp_ins[A, B](c, f, k, v, t))

def rbt_comp_insert[A, B](c: A => A => ordera):
      A => B => (rbta[A, B]) => rbta[A, B]
  =
  ((a: A) => (b: B) => (d: rbta[A, B]) =>
    rbt_comp_insert_with_key[A, B](c, ((_: A) => (_: B) => (nv: B) => nv), a, b,
                                    d))

def the[A](x0: Option[A]): A = x0 match {
  case Some(x2) => x2
}

def insertb[A : ccompare, B](xc: A, xd: B, xe: mapping_rbt[A, B]):
      mapping_rbt[A, B]
  =
  Mapping_RBT[A, B]((rbt_comp_insert[A, B](the[A =>
         A => ordera](ccompare[A]))).apply(xc).apply(xd).apply(impl_ofa[A,
                                 B](xe)))

def list_member[A](equal: A => A => Boolean, x1: List[A], y: A): Boolean =
  (equal, x1, y) match {
  case (equal, x :: xs, y) => (equal(x))(y) || list_member[A](equal, xs, y)
  case (equal, Nil, y) => false
}

def list_insert[A](equal: A => A => Boolean, x: A, xs: List[A]): List[A] =
  (if (list_member[A](equal, xs, x)) xs else x :: xs)

def inserta[A : ceq](xb: A, xc: set_dlist[A]): set_dlist[A] =
  Abs_dlist[A](list_insert[A](the[A => A => Boolean](ceq[A]), xb,
                               list_of_dlist[A](xc)))

def balance_right[A, B](a: rbta[A, B], k: A, x: B, xa3: rbta[A, B]): rbta[A, B]
  =
  (a, k, x, xa3) match {
  case (a, k, x, Branch(R(), b, s, y, c)) =>
    Branch[A, B](R(), a, k, x, Branch[A, B](B(), b, s, y, c))
  case (Branch(B(), a, k, x, b), s, y, Empty()) =>
    balance[A, B](Branch[A, B](R(), a, k, x, b), s, y, Empty[A, B]())
  case (Branch(B(), a, k, x, b), s, y, Branch(B(), va, vb, vc, vd)) =>
    balance[A, B](Branch[A, B](R(), a, k, x, b), s, y,
                   Branch[A, B](B(), va, vb, vc, vd))
  case (Branch(R(), a, k, x, Branch(B(), b, s, y, c)), t, z, Empty()) =>
    Branch[A, B](R(), balance[A, B](paint[A, B](R(), a), k, x, b), s, y,
                  Branch[A, B](B(), c, t, z, Empty[A, B]()))
  case (Branch(R(), a, k, x, Branch(B(), b, s, y, c)), t, z,
         Branch(B(), va, vb, vc, vd))
    => Branch[A, B](R(), balance[A, B](paint[A, B](R(), a), k, x, b), s, y,
                     Branch[A, B](B(), c, t, z,
                                   Branch[A, B](B(), va, vb, vc, vd)))
  case (Empty(), k, x, Empty()) => Empty[A, B]()
  case (Branch(R(), va, vb, vc, Empty()), k, x, Empty()) => Empty[A, B]()
  case (Branch(R(), va, vb, vc, Branch(R(), ve, vf, vg, vh)), k, x, Empty()) =>
    Empty[A, B]()
  case (Empty(), k, x, Branch(B(), va, vb, vc, vd)) => Empty[A, B]()
  case (Branch(R(), ve, vf, vg, Empty()), k, x, Branch(B(), va, vb, vc, vd)) =>
    Empty[A, B]()
  case (Branch(R(), ve, vf, vg, Branch(R(), vi, vj, vk, vl)), k, x,
         Branch(B(), va, vb, vc, vd))
    => Empty[A, B]()
}

def balance_left[A, B](x0: rbta[A, B], s: A, y: B, c: rbta[A, B]): rbta[A, B] =
  (x0, s, y, c) match {
  case (Branch(R(), a, k, x, b), s, y, c) =>
    Branch[A, B](R(), Branch[A, B](B(), a, k, x, b), s, y, c)
  case (Empty(), k, x, Branch(B(), a, s, y, b)) =>
    balance[A, B](Empty[A, B](), k, x, Branch[A, B](R(), a, s, y, b))
  case (Branch(B(), va, vb, vc, vd), k, x, Branch(B(), a, s, y, b)) =>
    balance[A, B](Branch[A, B](B(), va, vb, vc, vd), k, x,
                   Branch[A, B](R(), a, s, y, b))
  case (Empty(), k, x, Branch(R(), Branch(B(), a, s, y, b), t, z, c)) =>
    Branch[A, B](R(), Branch[A, B](B(), Empty[A, B](), k, x, a), s, y,
                  balance[A, B](b, t, z, paint[A, B](R(), c)))
  case (Branch(B(), va, vb, vc, vd), k, x,
         Branch(R(), Branch(B(), a, s, y, b), t, z, c))
    => Branch[A, B](R(), Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), k,
                                       x, a),
                     s, y, balance[A, B](b, t, z, paint[A, B](R(), c)))
  case (Empty(), k, x, Empty()) => Empty[A, B]()
  case (Empty(), k, x, Branch(R(), Empty(), vb, vc, vd)) => Empty[A, B]()
  case (Empty(), k, x, Branch(R(), Branch(R(), ve, vf, vg, vh), vb, vc, vd)) =>
    Empty[A, B]()
  case (Branch(B(), va, vb, vc, vd), k, x, Empty()) => Empty[A, B]()
  case (Branch(B(), va, vb, vc, vd), k, x, Branch(R(), Empty(), vf, vg, vh)) =>
    Empty[A, B]()
  case (Branch(B(), va, vb, vc, vd), k, x,
         Branch(R(), Branch(R(), vi, vj, vk, vl), vf, vg, vh))
    => Empty[A, B]()
}

def combine[A, B](xa0: rbta[A, B], x: rbta[A, B]): rbta[A, B] = (xa0, x) match {
  case (Empty(), x) => x
  case (Branch(v, va, vb, vc, vd), Empty()) => Branch[A, B](v, va, vb, vc, vd)
  case (Branch(R(), a, k, x, b), Branch(R(), c, s, y, d)) =>
    (combine[A, B](b, c) match {
       case Empty() =>
         Branch[A, B](R(), a, k, x, Branch[A, B](R(), Empty[A, B](), s, y, d))
       case Branch(R(), b2, t, z, c2) =>
         Branch[A, B](R(), Branch[A, B](R(), a, k, x, b2), t, z,
                       Branch[A, B](R(), c2, s, y, d))
       case Branch(B(), b2, t, z, c2) =>
         Branch[A, B](R(), a, k, x,
                       Branch[A, B](R(), Branch[A, B](B(), b2, t, z, c2), s, y,
                                     d))
     })
  case (Branch(B(), a, k, x, b), Branch(B(), c, s, y, d)) =>
    (combine[A, B](b, c) match {
       case Empty() =>
         balance_left[A, B](a, k, x, Branch[A, B](B(), Empty[A, B](), s, y, d))
       case Branch(R(), b2, t, z, c2) =>
         Branch[A, B](R(), Branch[A, B](B(), a, k, x, b2), t, z,
                       Branch[A, B](B(), c2, s, y, d))
       case Branch(B(), b2, t, z, c2) =>
         balance_left[A, B](a, k, x,
                             Branch[A, B](B(), Branch[A, B](B(), b2, t, z, c2),
   s, y, d))
     })
  case (Branch(B(), va, vb, vc, vd), Branch(R(), b, k, x, c)) =>
    Branch[A, B](R(), combine[A, B](Branch[A, B](B(), va, vb, vc, vd), b), k, x,
                  c)
  case (Branch(R(), a, k, x, b), Branch(B(), va, vb, vc, vd)) =>
    Branch[A, B](R(), a, k, x,
                  combine[A, B](b, Branch[A, B](B(), va, vb, vc, vd)))
}

def rbt_comp_del_from_right[A, B](c: A => A => ordera, x: A, a: rbta[A, B],
                                   y: A, s: B, xa5: rbta[A, B]):
      rbta[A, B]
  =
  (c, x, a, y, s, xa5) match {
  case (c, x, a, y, s, Branch(B(), lt, z, v, rt)) =>
    balance_right[A, B](a, y, s,
                         rbt_comp_del[A, B](c, x,
     Branch[A, B](B(), lt, z, v, rt)))
  case (c, x, a, y, s, Empty()) =>
    Branch[A, B](R(), a, y, s, rbt_comp_del[A, B](c, x, Empty[A, B]()))
  case (c, x, a, y, s, Branch(R(), va, vb, vc, vd)) =>
    Branch[A, B](R(), a, y, s,
                  rbt_comp_del[A, B](c, x, Branch[A, B](R(), va, vb, vc, vd)))
}

def rbt_comp_del_from_left[A, B](c: A => A => ordera, x: A, xa2: rbta[A, B],
                                  y: A, s: B, b: rbta[A, B]):
      rbta[A, B]
  =
  (c, x, xa2, y, s, b) match {
  case (c, x, Branch(B(), lt, z, v, rt), y, s, b) =>
    balance_left[A, B](rbt_comp_del[A, B](c, x,
   Branch[A, B](B(), lt, z, v, rt)),
                        y, s, b)
  case (c, x, Empty(), y, s, b) =>
    Branch[A, B](R(), rbt_comp_del[A, B](c, x, Empty[A, B]()), y, s, b)
  case (c, x, Branch(R(), va, vb, vc, vd), y, s, b) =>
    Branch[A, B](R(), rbt_comp_del[A, B](c, x,
  Branch[A, B](R(), va, vb, vc, vd)),
                  y, s, b)
}

def rbt_comp_del[A, B](c: A => A => ordera, x: A, xa2: rbta[A, B]): rbta[A, B] =
  (c, x, xa2) match {
  case (c, x, Empty()) => Empty[A, B]()
  case (c, x, Branch(uu, a, y, s, b)) =>
    ((c(x))(y) match {
       case Eq() => combine[A, B](a, b)
       case Lt() => rbt_comp_del_from_left[A, B](c, x, a, y, s, b)
       case Gt() => rbt_comp_del_from_right[A, B](c, x, a, y, s, b)
     })
}

def rbt_comp_delete[A, B](c: A => A => ordera, k: A, t: rbta[A, B]): rbta[A, B]
  =
  paint[A, B](B(), rbt_comp_del[A, B](c, k, t))

def delete[A : ccompare, B](xb: A, xc: mapping_rbt[A, B]): mapping_rbt[A, B] =
  Mapping_RBT[A, B](rbt_comp_delete[A, B](the[A => A => ordera](ccompare[A]),
   xb, impl_ofa[A, B](xc)))

def list_remove1[A](equal: A => A => Boolean, x: A, xa2: List[A]): List[A] =
  (equal, x, xa2) match {
  case (equal, x, y :: xs) =>
    (if ((equal(x))(y)) xs else y :: list_remove1[A](equal, x, xs))
  case (equal, x, Nil) => Nil
}

def removea[A : ceq](xb: A, xc: set_dlist[A]): set_dlist[A] =
  Abs_dlist[A](list_remove1[A](the[A => A => Boolean](ceq[A]), xb,
                                list_of_dlist[A](xc)))

def remove[A : ceq : ccompare](x: A, xa1: set[A]): set[A] = (x, xa1) match {
  case (x, Complement(a)) => Complement[A](insert[A](x, a))
  case (x, RBT_set(rbt)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("remove RBT_set: ccompare = None");
           (((_: Unit) => remove[A](x, RBT_set[A](rbt)))).apply(()) }
       case Some(_) => RBT_set[A](delete[A, Unit](x, rbt))
     })
  case (x, DList_set(dxs)) =>
    (ceq[A] match {
       case None =>
         { sys.error("remove DList_set: ceq = None");
           (((_: Unit) => remove[A](x, DList_set[A](dxs)))).apply(()) }
       case Some(_) => DList_set[A](removea[A](x, dxs))
     })
  case (x, Collect_set(a)) =>
    (ceq[A] match {
       case None =>
         { sys.error("remove Collect: ceq = None");
           (((_: Unit) => remove[A](x, Collect_set[A](a)))).apply(()) }
       case Some(eq) =>
         Collect_set[A](((b: A) => fun_upd[A, Boolean](eq, a, x, false, b)))
     })
}

def insert[A : ceq : ccompare](xa: A, x1: set[A]): set[A] = (xa, x1) match {
  case (xa, Complement(x)) => Complement[A](remove[A](xa, x))
  case (x, RBT_set(rbt)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("insert RBT_set: ccompare = None");
           (((_: Unit) => insert[A](x, RBT_set[A](rbt)))).apply(()) }
       case Some(_) => RBT_set[A](insertb[A, Unit](x, (), rbt))
     })
  case (x, DList_set(dxs)) =>
    (ceq[A] match {
       case None =>
         { sys.error("insert DList_set: ceq = None");
           (((_: Unit) => insert[A](x, DList_set[A](dxs)))).apply(()) }
       case Some(_) => DList_set[A](inserta[A](x, dxs))
     })
  case (x, Set_Monad(xs)) => Set_Monad[A](x :: xs)
  case (x, Collect_set(a)) =>
    (ceq[A] match {
       case None =>
         { sys.error("insert Collect_set: ceq = None");
           (((_: Unit) => insert[A](x, Collect_set[A](a)))).apply(()) }
       case Some(eq) =>
         Collect_set[A](((b: A) => fun_upd[A, Boolean](eq, a, x, true, b)))
     })
}

def memberb[A : ceq](xa: set_dlist[A]): A => Boolean =
  ((a: A) =>
    list_member[A](the[A => A => Boolean](ceq[A]), list_of_dlist[A](xa), a))

def rbt_comp_lookup[A, B](c: A => A => ordera, x1: rbta[A, B], k: A): Option[B]
  =
  (c, x1, k) match {
  case (c, Empty(), k) => None
  case (c, Branch(uu, l, x, y, r), k) =>
    ((c(k))(x) match {
       case Eq() => Some[B](y)
       case Lt() => rbt_comp_lookup[A, B](c, l, k)
       case Gt() => rbt_comp_lookup[A, B](c, r, k)
     })
}

def lookup[A : ccompare, B](xa: mapping_rbt[A, B]): A => Option[B] =
  ((a: A) =>
    rbt_comp_lookup[A, B](the[A => A => ordera](ccompare[A]),
                           impl_ofa[A, B](xa), a))

def membera[A : ccompare](t: mapping_rbt[A, Unit], x: A): Boolean =
  equal_optiona[Unit]((lookup[A, Unit](t)).apply(x), Some[Unit](()))

def member[A : ceq : ccompare](x: A, xa1: set[A]): Boolean = (x, xa1) match {
  case (x, Set_Monad(xs)) =>
    (ceq[A] match {
       case None =>
         { sys.error("member Set_Monad: ceq = None");
           (((_: Unit) => member[A](x, Set_Monad[A](xs)))).apply(()) }
       case Some(eq) => list_member[A](eq, xs, x)
     })
  case (xa, Complement(x)) => ! (member[A](xa, x))
  case (x, RBT_set(rbt)) => membera[A](rbt, x)
  case (x, DList_set(dxs)) => (memberb[A](dxs)).apply(x)
  case (x, Collect_set(a)) => a(x)
}

def filter[A](p: A => Boolean, x1: List[A]): List[A] = (p, x1) match {
  case (p, Nil) => Nil
  case (p, x :: xs) => (if (p(x)) x :: filter[A](p, xs) else filter[A](p, xs))
}

def Collect[A : cenum](p: A => Boolean): set[A] =
  (cEnum[A] match {
     case None => Collect_set[A](p)
     case Some((enuma, _)) => Set_Monad[A](filter[A](p, enuma))
   })

def update[A : equal, B](k: A, v: B, x2: List[(A, B)]): List[(A, B)] =
  (k, v, x2) match {
  case (k, v, Nil) => List((k, v))
  case (k, v, p :: ps) =>
    (if (eq[A](fst[A, B](p), k)) (k, v) :: ps else p :: update[A, B](k, v, ps))
}

def foldli[A, B](x0: List[A], c: B => Boolean, f: A => B => B, sigma: B): B =
  (x0, c, f, sigma) match {
  case (Nil, c, f, sigma) => sigma
  case (x :: xs, c, f, sigma) =>
    (if (c(sigma)) foldli[A, B](xs, c, f, (f(x))(sigma)) else sigma)
}

def product[A, B](x0: List[A], uu: List[B]): List[(A, B)] = (x0, uu) match {
  case (Nil, uu) => Nil
  case (x :: xs, ys) =>
    map[B, (A, B)](((a: B) => (x, a)), ys) ++ product[A, B](xs, ys)
}

def remove1[A : equal](x: A, xa1: List[A]): List[A] = (x, xa1) match {
  case (x, Nil) => Nil
  case (x, y :: xs) => (if (eq[A](x, y)) xs else y :: remove1[A](x, xs))
}

def of_fun[A](f: nat => A, n: nat): Array.T[A] =
  (integer_of_nat(n),
    comp[nat, A,
          BigInt](f, ((a: BigInt) =>
                       nat_of_integer(a)))) match { case (a,b) => Array.make(a)(b) }

def unzip[A, B](x0: List[(A, B)]): (List[A], List[B]) = x0 match {
  case Nil => (Nil, Nil)
  case (x, y) :: xs => {
                         val (as, bs) = unzip[A, B](xs): ((List[A], List[B]));
                         (x :: as, y :: bs)
                       }
}

def of_phantom[A, B](x0: phantom[A, B]): B = x0 match {
  case phantoma(x) => x
}

def emptya[A : ccompare, B]: mapping_rbt[A, B] =
  Mapping_RBT[A, B](Empty[A, B]())

def empty[A : ceq]: set_dlist[A] = Abs_dlist[A](Nil)

def set_empty_choose[A : ceq : ccompare]: set[A] =
  (ccompare[A] match {
     case None => (ceq[A] match {
                     case None => Set_Monad[A](Nil)
                     case Some(_) => DList_set[A](empty[A])
                   })
     case Some(_) => RBT_set[A](emptya[A, Unit])
   })

def set_empty[A : ceq : ccompare](x0: set_impla): set[A] = x0 match {
  case set_Choose() => set_empty_choose[A]
  case set_Monad() => Set_Monad[A](Nil)
  case set_RBT() => RBT_set[A](emptya[A, Unit])
  case set_DList() => DList_set[A](empty[A])
  case set_Collect() => Collect_set[A](((_: A) => false))
}

def set_aux[A : ceq : ccompare](impl: set_impla): (List[A]) => set[A] = impl
  match {
  case set_Monad() => ((a: List[A]) => Set_Monad[A](a))
  case set_Choose() =>
    (ccompare[A] match {
       case None =>
         (ceq[A] match {
            case None => ((a: List[A]) => Set_Monad[A](a))
            case Some(_) =>
              ((a: List[A]) =>
                foldl[set[A],
                       A](((s: set[A]) => (x: A) => insert[A](x, s)),
                           DList_set[A](empty[A]), a))
          })
       case Some(_) =>
         ((a: List[A]) =>
           foldl[set[A],
                  A](((s: set[A]) => (x: A) => insert[A](x, s)),
                      RBT_set[A](emptya[A, Unit]), a))
     })
  case impl =>
    ((a: List[A]) =>
      foldl[set[A],
             A](((s: set[A]) => (x: A) => insert[A](x, s)), set_empty[A](impl),
                 a))
}

def set[A : ceq : ccompare : set_impl](xs: List[A]): set[A] =
  (set_aux[A](of_phantom[A, set_impla](set_impl[A]))).apply(xs)

def inorder[A, B](x0: tree[(A, B)]): List[A] = x0 match {
  case Leaf() => Nil
  case Node(l, (a, uu), r) => inorder[A, B](l) ++ (a :: inorder[A, B](r))
}

def enumerate[A](n: nat, x1: List[A]): List[(nat, A)] = (n, x1) match {
  case (n, x :: xs) => (n, x) :: enumerate[A](Suc(n), xs)
  case (n, Nil) => Nil
}

def partition[A](p: A => Boolean, x1: List[A]): (List[A], List[A]) = (p, x1)
  match {
  case (p, Nil) => (Nil, Nil)
  case (p, x :: xs) =>
    {
      val (yes, no) = partition[A](p, xs): ((List[A], List[A]));
      (if (p(x)) (x :: yes, no) else (yes, x :: no))
    }
}

def is_none[A](x0: Option[A]): Boolean = x0 match {
  case Some(x) => false
  case None => true
}

def of_bool[A : zero_neq_one](x0: Boolean): A = x0 match {
  case true => one[A]
  case false => zero[A]
}

def integer_of_char(x0: char): BigInt = x0 match {
  case Char(b0, b1, b2, b3, b4, b5, b6, b7) =>
    ((((((of_bool[BigInt](b7) * BigInt(2) + of_bool[BigInt](b6)) * BigInt(2) +
          of_bool[BigInt](b5)) *
          BigInt(2) +
         of_bool[BigInt](b4)) *
         BigInt(2) +
        of_bool[BigInt](b3)) *
        BigInt(2) +
       of_bool[BigInt](b2)) *
       BigInt(2) +
      of_bool[BigInt](b1)) *
      BigInt(2) +
      of_bool[BigInt](b0)
}

def implode(cs: List[char]): String =
  "" ++ (map[char,
              BigInt](((a: char) => integer_of_char(a)),
                       cs)).map((k: BigInt) => if (BigInt(0) <= k && k < BigInt(128)) k.charValue else sys.error("Non-ASCII character in literal"))

def gen_length[A](n: nat, x1: List[A]): nat = (n, x1) match {
  case (n, x :: xs) => gen_length[A](Suc(n), xs)
  case (n, Nil) => n
}

def map_filter[A, B](f: A => Option[B], x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) => (f(x) match {
                          case None => map_filter[A, B](f, xs)
                          case Some(y) => y :: map_filter[A, B](f, xs)
                        })
}

def endl: List[char] =
  List(Char(false, true, false, true, false, false, false, false))

def Rep_rat_pair(x0: rat_pair): (int, int) = x0 match {
  case Abs_rat_pair(x) => x
}

def mul_rat_pair(xb: rat_pair, xc: rat_pair): rat_pair =
  Abs_rat_pair(({
                  val (n1, d1) = Rep_rat_pair(xb): ((int, int));
                  ((a: (int, int)) => {
val (n2, d2) = a: ((int, int));
(times_int(n1, n2), times_int(d1, d2))
                                      })
                })(Rep_rat_pair(xc)))

def mul_real_code(x0: real_code, x1: real_code): real_code = (x0, x1) match {
  case (Frcta(r1), Frcta(r2)) => Frcta(mul_rat_pair(r1, r2))
}

def add_rat_pair(xb: rat_pair, xc: rat_pair): rat_pair =
  Abs_rat_pair(({
                  val (n1, d1) = Rep_rat_pair(xb): ((int, int));
                  ((a: (int, int)) =>
                    {
                      val (n2, d2) = a: ((int, int));
                      (plus_int(times_int(n1, d2), times_int(n2, d1)),
                        times_int(d1, d2))
                    })
                })(Rep_rat_pair(xc)))

def add_real_code(x0: real_code, x1: real_code): real_code = (x0, x1) match {
  case (Frcta(r1), Frcta(r2)) => Frcta(add_rat_pair(r1, r2))
}

def quotient_ofa(xa: rat): rat_pair = Abs_rat_pair(quotient_of(xa))

def real_to_code(x0: real): real_code = x0 match {
  case Ratreal(x) => Frcta(quotient_ofa(x))
}

def mult_add(x: real, y: real, acc: real_code): real_code =
  add_real_code(mul_real_code(real_to_code(y), real_to_code(x)), acc)

def list_update[A](x0: List[A], i: nat, y: A): List[A] = (x0, i, y) match {
  case (Nil, i, y) => Nil
  case (x :: xs, i, y) =>
    (if (equal_nata(i, zero_nata)) y :: xs
      else x :: list_update[A](xs, minus_nata(i, one_nata), y))
}

def rbt_init[A, B, C]: (rbta[A, B]) => (List[(C, rbta[A, B])], rbta[A, B]) =
  ((a: rbta[A, B]) => (Nil, a))

def init[A : ccompare, B, C](xa: mapping_rbt[A, B]):
      (List[(C, rbta[A, B])], rbta[A, B])
  =
  rbt_init[A, B, C].apply(impl_ofa[A, B](xa))

def default_sol_vec_ops_uu_set_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_constr_map_ops_scoped_ereal_ops_uu_ste_ops_scoped_real_ops_uu_uu_uu(a:
            api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
           b: List[((Array.T[nat], nat), nat)],
           c: nat => nat => (((Array.T[nat], nat)) => real, nat)):
      (hashmap[var_code[(List[Option[nat]], (nat, Boolean)), List[Option[nat]]],
                real],
        real)
  =
  sys.error("Code_Export.default_sol_vec_ops_uu_set_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_constr_map_ops_scoped_ereal_ops_uu_ste_ops_scoped_real_ops_uu_uu_uu")

def api_input_dims[A, B, C](x0: api_input_ext[A, B, C]): nat = x0 match {
  case api_input_exta(api_input_dims, api_input_doms, api_input_t_max_code,
                       api_input_epsilon_code, api_input_rewards_code_fn,
                       api_input_rewards_scope_code, api_input_reward_dim_code,
                       api_input_actions_code, api_input_d_code,
                       api_input_transitions_code_fn,
                       api_input_transitions_scopes_code, api_input_l_code,
                       api_input_h_code_fn, api_input_h_scope_code,
                       api_input_h_dim_code, api_input_effects_code, more)
    => api_input_dims
}

def vec_op_alpha[A, B, C, D](x0: vec_ops_ext[A, B, C, D]): A => nat => Option[B]
  =
  x0 match {
  case vec_ops_exta(vec_op_alpha, vec_op_scope, vec_op_idx, vec_op_invar,
                     vec_op_empty, vec_op_update, vec_op_restr, more)
    => vec_op_alpha
}

def power_aux(i: nat, j: nat, acc: nat): nat =
  (if (equal_nata(j, zero_nata)) acc
    else power_aux(i, minus_nata(j, one_nata), times_nata(acc, i)))

def power_tr(i: nat, j: nat): nat = power_aux(i, j, one_nata)

def push_bit_nat(n: nat, m: nat): nat =
  times_nata(m, power_tr(nat_of_integer(BigInt(2)), n))

def or_nat(m: nat, n: nat): nat =
  (if (equal_nata(m, zero_nata)) n
    else (if (equal_nata(n, zero_nata)) m
           else plus_nata(max[nat](modulo_nata(m, nat_of_integer(BigInt(2))),
                                    modulo_nata(n, nat_of_integer(BigInt(2)))),
                           times_nata(nat_of_integer(BigInt(2)),
                                       or_nat(divide_nata(m,
                   nat_of_integer(BigInt(2))),
       divide_nata(n, nat_of_integer(BigInt(2))))))))

def set_bit_nat(m: nat, n: nat): nat = or_nat(n, push_bit_nat(m, one_nata))

def dvd[A : equal : semidom_modulo](a: A, b: A): Boolean =
  eq[A](modulo[A](b, a), zero[A])

def bit_nat(m: nat, n: nat): Boolean =
  ! (dvd[nat](nat_of_integer(BigInt(2)),
               divide_nata(m, power_tr(nat_of_integer(BigInt(2)), n))))

def api_input_doms[A, B, C](x0: api_input_ext[A, B, C]): nat => nat = x0 match {
  case api_input_exta(api_input_dims, api_input_doms, api_input_t_max_code,
                       api_input_epsilon_code, api_input_rewards_code_fn,
                       api_input_rewards_scope_code, api_input_reward_dim_code,
                       api_input_actions_code, api_input_d_code,
                       api_input_transitions_code_fn,
                       api_input_transitions_scopes_code, api_input_l_code,
                       api_input_h_code_fn, api_input_h_scope_code,
                       api_input_h_dim_code, api_input_effects_code, more)
    => api_input_doms
}

def bs_to_list_aux(acc: List[nat], i: nat, s: nat): List[nat] =
  (if (equal_nata(s, zero_nata)) acc
    else bs_to_list_aux((if (! (dvd[nat](nat_of_integer(BigInt(2)), s)))
                          i :: acc else acc),
                         Suc(i), divide_nata(s, nat_of_integer(BigInt(2)))))

def bs_to_list: nat => List[nat] =
  ((a: nat) => bs_to_list_aux(Nil, zero_nata, a))

def bs_iteratei[A](x: nat): (A => Boolean) => (nat => A => A) => A => A =
  ((a: A => Boolean) => (b: nat => A => A) => (c: A) =>
    foldli[nat, A](bs_to_list.apply(x), a, b, c))

def iteratei_bset_op_list_it_bs_basic_ops[A](s: nat):
      (A => Boolean) => (nat => A => A) => A => A
  =
  bs_iteratei[A](s)

def g_inter_bs_basic_ops(s1: nat, s2: nat): nat =
  (iteratei_bset_op_list_it_bs_basic_ops[nat](s1)).apply(((_: nat) =>
                   true)).apply(((x: nat) => (s: nat) =>
                                  (if (bit_nat(s2, x)) set_bit_nat(x, s)
                                    else s))).apply(zero_nata)

def g_ball_bs_basic_ops(s: nat, p: nat => Boolean): Boolean =
  (iteratei_bset_op_list_it_bs_basic_ops[Boolean](s)).apply(((c: Boolean) =>
                      c)).apply(((x: nat) => (_: Boolean) => p(x))).apply(true)

def vec_ops_set_ops_api_input_dims_uu_api_input_doms_uu(api_input:
                  api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit]):
      vec_ops_ext[(Array.T[nat], nat), nat, nat, Unit]
  =
  vec_ops_exta[(Array.T[nat], nat), nat, nat,
                Unit](((a: (Array.T[nat], nat)) =>
                        {
                          val (v, s) = a: ((Array.T[nat], nat));
                          ((i: nat) =>
                            (if (bit_nat(s, i)) Some[nat](sub[nat](v, i))
                              else None))
                        }),
                       ((a: (Array.T[nat], nat)) => snd[Array.T[nat], nat](a)),
                       ((a: (Array.T[nat], nat)) =>
                         {
                           val (v, _) = a: ((Array.T[nat], nat));
                           ((aa: nat) => sub[nat](v, aa))
                         }),
                       ((a: (Array.T[nat], nat)) =>
                         {
                           val (v, s) = a: ((Array.T[nat], nat));
                           equal_nata(length[nat](v),
                                       api_input_dims[nat,
               (DiffArray.T[Option[real]], nat), Unit](api_input)) &&
                             (true &&
                               (g_ball_bs_basic_ops(s,
             ((i: nat) =>
               less_nat(i, api_input_dims[nat, (DiffArray.T[Option[real]], nat),
   Unit](api_input)))) &&
                                 g_ball_bs_basic_ops(s,
              ((i: nat) =>
                less_nat(sub[nat](v, i),
                          (api_input_doms[nat, (DiffArray.T[Option[real]], nat),
   Unit](api_input)).apply(i))))))
                         }),
                       (of_fun[nat](((_: nat) => zero_nata),
                                     api_input_dims[nat,
             (DiffArray.T[Option[real]], nat), Unit](api_input)),
                         zero_nata),
                       ((a: (Array.T[nat], nat)) =>
                         {
                           val (v, s) = a: ((Array.T[nat], nat));
                           ((i: nat) => (y: nat) =>
                             (Array.init_list[nat](list_update[nat](list_of[nat](v),
                             i, y)),
                               set_bit_nat(i, s)))
                         }),
                       ((a: (Array.T[nat], nat)) =>
                         {
                           val (v, s) = a: ((Array.T[nat], nat));
                           ((sa: nat) => (v, g_inter_bs_basic_ops(s, sa)))
                         }),
                       ())

def vec_ops_uua(api_input:
                  api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit]):
      vec_ops_ext[(Array.T[nat], nat), nat, nat, Unit]
  =
  vec_ops_set_ops_api_input_dims_uu_api_input_doms_uu(api_input)

def vec_to_list_vec_ops_uu_api_input_dims_uu(api_input:
       api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
      v: (Array.T[nat], nat)):
      List[Option[nat]]
  =
  map[nat, Option[nat]]((vec_op_alpha[(Array.T[nat], nat), nat, nat,
                                       Unit](vec_ops_uua(api_input))).apply(v),
                         upt.apply(zero_nata).apply(api_input_dims[nat,
                            (DiffArray.T[Option[real]], nat), Unit](api_input)))

def show_state_vec_ops_uu_api_input_dims_uu(api_input:
      api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
     x: (Array.T[nat], nat)):
      List[Option[nat]]
  =
  vec_to_list_vec_ops_uu_api_input_dims_uu(api_input, x)

def bit_uint32(x: Int, n: nat): Boolean =
  less_nat(n, nat_of_integer(BigInt(32))) &&
    Uint32.test_bit(x, integer_of_nat(n))

def integer_of_uint32(n: Int): BigInt =
  (if (bit_uint32(n, nat_of_integer(BigInt(31))))
    BigInt(n & BigInt(2147483647).intValue) | BigInt("2147483648")
    else BigInt(n))

def nat_of_uint32(x: Int): nat = nat_of_integer(integer_of_uint32(x))

def nat_of_hashcode: Int => nat = ((a: Int) => nat_of_uint32(a))

def bounded_hashcode_nat[A : hashable](n: nat, x: A): nat =
  modulo_nata(nat_of_hashcode.apply(hashcode[A](x)), n)

def array_length[A]: (DiffArray.T[A]) => nat =
  comp[BigInt, nat,
        DiffArray.T[A]](((a: BigInt) => nat_of_integer(a)),
                         ((a: DiffArray.T[A]) => DiffArray.length(a).toInt))

def array_set[A](a: DiffArray.T[A]): nat => A => DiffArray.T[A] =
  comp[BigInt, A => DiffArray.T[A],
        nat](((b: BigInt) => (c: A) => DiffArray.set(a,b.toInt,c)),
              ((aa: nat) => integer_of_nat(aa)))

def array_get[A](a: DiffArray.T[A]): nat => A =
  comp[BigInt, A,
        nat](((b: BigInt) => DiffArray.get(a,b.toInt)),
              ((aa: nat) => integer_of_nat(aa)))

def ahm_update_aux[A : equal : hashable, B](x0: hashmapa[A, B], k: A, v: B):
      hashmapa[A, B]
  =
  (x0, k, v) match {
  case (HashMapa(a, n), k, v) =>
    {
      val h =
        bounded_hashcode_nat[A](array_length[List[(A, B)]].apply(a), k): nat
      val m = (array_get[List[(A, B)]](a)).apply(h): (List[(A, B)])
      val insert = is_none[B](map_of[A, B](m, k)): Boolean;
      HashMapa[A, B]((array_set[List[(A, B)]](a)).apply(h).apply(update[A,
                                 B](k, v, m)),
                      (if (insert) plus_nata(n, one_nata) else n))
    }
}

def idx_iteratei_aux_array_get[A, B](sz: nat, i: nat, l: DiffArray.T[A],
                                      c: B => Boolean, f: A => B => B,
                                      sigma: B):
      B
  =
  (if (equal_nata(i, zero_nata) || ! (c(sigma))) sigma
    else idx_iteratei_aux_array_get[A, B](sz, minus_nata(i, one_nata), l, c, f,
   (f((array_get[A](l)).apply(minus_nata(sz, i))))(sigma)))

def idx_iteratei_array_length_array_get[A,
 B](l: DiffArray.T[A], c: B => Boolean, f: A => B => B, sigma: B):
      B
  =
  idx_iteratei_aux_array_get[A, B](array_length[A].apply(l),
                                    array_length[A].apply(l), l, c, f, sigma)

def ahm_iteratei_aux[A : hashable, B,
                      C](a: DiffArray.T[(List[(A, B)])], c: C => Boolean,
                          f: ((A, B)) => C => C, sigma: C):
      C
  =
  idx_iteratei_array_length_array_get[List[(A, B)],
                                       C](a, c,
   ((x: List[(A, B)]) => ((aa: C) => foldli[(A, B), C](x, c, f, aa))), sigma)

def ahm_rehash_auxa[A : hashable,
                     B](n: nat, kv: (A, B), a: DiffArray.T[(List[(A, B)])]):
      DiffArray.T[(List[(A, B)])]
  =
  {
    val h = bounded_hashcode_nat[A](n, fst[A, B](kv)): nat;
    (array_set[List[(A, B)]](a)).apply(h).apply(kv ::
          (array_get[List[(A, B)]](a)).apply(h))
  }

def new_array[A](v: A): nat => DiffArray.T[A] =
  comp[BigInt, DiffArray.T[A],
        nat](((a: BigInt) => DiffArray.new_array(v,a.toInt)),
              ((a: nat) => integer_of_nat(a)))

def ahm_rehash_aux[A : hashable, B](a: DiffArray.T[(List[(A, B)])], sz: nat):
      DiffArray.T[(List[(A, B)])]
  =
  ahm_iteratei_aux[A, B,
                    DiffArray.T[(List[(A,
B)])]](a, ((_: DiffArray.T[(List[(A, B)])]) => true),
        ((aa: (A, B)) => (b: DiffArray.T[(List[(A, B)])]) =>
          ahm_rehash_auxa[A, B](sz, aa, b)),
        (new_array[List[(A, B)]](Nil)).apply(sz))

def ahm_rehash[A : hashable, B](x0: hashmapa[A, B], sz: nat): hashmapa[A, B] =
  (x0, sz) match {
  case (HashMapa(a, n), sz) => HashMapa[A, B](ahm_rehash_aux[A, B](a, sz), n)
}

def load_factor: nat = nat_of_integer(BigInt(75))

def ahm_filled[A : hashable, B](x0: hashmapa[A, B]): Boolean = x0 match {
  case HashMapa(a, n) =>
    less_eq_nat(times_nata(array_length[List[(A, B)]].apply(a), load_factor),
                 times_nata(n, nat_of_integer(BigInt(100))))
}

def hm_grow[A : hashable, B](x0: hashmapa[A, B]): nat = x0 match {
  case HashMapa(a, n) =>
    plus_nata(times_nata(nat_of_integer(BigInt(2)),
                          array_length[List[(A, B)]].apply(a)),
               nat_of_integer(BigInt(3)))
}

def ahm_updatea[A : equal : hashable, B](k: A, v: B, hm: hashmapa[A, B]):
      hashmapa[A, B]
  =
  {
    val hma = ahm_update_aux[A, B](hm, k, v): (hashmapa[A, B]);
    (if (ahm_filled[A, B](hma)) ahm_rehash[A, B](hma, hm_grow[A, B](hma))
      else hma)
  }

def impl_of[B : hashable, A](x0: hashmap[B, A]): hashmapa[B, A] = x0 match {
  case HashMap(x) => x
}

def ahm_update[A : equal : hashable, B](k: A, v: B, hm: hashmap[A, B]):
      hashmap[A, B]
  =
  HashMap[A, B](ahm_updatea[A, B](k, v, impl_of[A, B](hm)))

def new_hashmap_with[A : hashable, B](size: nat): hashmapa[A, B] =
  HashMapa[A, B]((new_array[List[(A, B)]](Nil)).apply(size), zero_nata)

def ahm_emptya[A : hashable, B]: Unit => hashmapa[A, B] =
  ((_: Unit) => new_hashmap_with[A, B](def_hashmap_size[A](typea[A]())))

def ahm_empty_const[A : hashable, B]: hashmap[A, B] =
  HashMap[A, B](ahm_emptya[A, B].apply(()))

def ahm_empty[A : hashable, B]: Unit => hashmap[A, B] =
  ((_: Unit) => ahm_empty_const[A, B])

def g_list_to_map_ahm_basic_ops[A : equal : hashable, B](l: List[(A, B)]):
      hashmap[A, B]
  =
  foldl[hashmap[A, B],
         (A, B)](((m: hashmap[A, B]) => (a: (A, B)) =>
                   {
                     val (k, v) = a: ((A, B));
                     ahm_update[A, B](k, v, m)
                   }),
                  ahm_empty[A, B].apply(()), rev[(A, B)](l))

def constr_eq_from_list_constr_map_ops(xs:
 List[(var_code[(List[Option[nat]], (nat, Boolean)), List[Option[nat]]], real)],
rhs: real):
      Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                                    List[Option[nat]]],
                           real]]
  =
  Constr_Eq[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                              List[Option[nat]]],
                     real]](g_list_to_map_ahm_basic_ops[var_code[(List[Option[nat]],
                           (nat, Boolean)),
                          List[Option[nat]]],
                 real](xs),
                             rhs)

def constr_b_code_constr_map_ops_Pair_show_state_vec_ops_uu_api_input_dims_uu_uu_Pair_uu_uu_show_state_vec_ops_uu_api_input_dims_uu(api_input:
              api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
             t_code: (Array.T[nat], nat), a_code: nat, pos: Boolean,
             z: (Array.T[nat], nat), j: nat, rhs: real):
      Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                                    List[Option[nat]]],
                           real]]
  =
  constr_eq_from_list_constr_map_ops(List((var_f[(List[Option[nat]],
           (nat, Boolean)),
          List[Option[nat]]]((show_state_vec_ops_uu_api_input_dims_uu(api_input,
                               t_code),
                               (a_code, pos)),
                              f_b_code(j),
                              show_state_vec_ops_uu_api_input_dims_uu(api_input,
                               z)),
    one_reala)),
                                      rhs)

def vec_op_update[A, B, C, D](x0: vec_ops_ext[A, B, C, D]): A => nat => B => A =
  x0 match {
  case vec_ops_exta(vec_op_alpha, vec_op_scope, vec_op_idx, vec_op_invar,
                     vec_op_empty, vec_op_update, vec_op_restr, more)
    => vec_op_update
}

def assignments_impl_aux_vec_ops_uu_api_input_doms_uu(api_input:
                api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
               x1: List[nat], v: (Array.T[nat], nat)):
      List[(Array.T[nat], nat)]
  =
  (api_input, x1, v) match {
  case (api_input, Nil, v) => List(v)
  case (api_input, i :: is, v) =>
    maps[nat, (Array.T[nat],
                nat)](((y: nat) =>
                        assignments_impl_aux_vec_ops_uu_api_input_doms_uu(api_input,
                                   is, (vec_op_update[(Array.T[nat], nat), nat,
               nat, Unit](vec_ops_uua(api_input))).apply(v).apply(i).apply(y))),
                       upt.apply(zero_nata).apply((api_input_doms[nat,
                           (DiffArray.T[Option[real]], nat),
                           Unit](api_input)).apply(i)))
}

def rev_iterateoi_bset_op_rev_list_it_bs_basic_ops[A](s: nat):
      (A => Boolean) => (nat => A => A) => A => A
  =
  bs_iteratei[A](s)

def g_to_sorted_list_bs_basic_ops(s: nat): List[nat] =
  (rev_iterateoi_bset_op_rev_list_it_bs_basic_ops[List[nat]](s)).apply(((_:
                                   List[nat])
                                  =>
                                 true)).apply(((a: nat) => (b: List[nat]) =>
        a :: b)).apply(Nil)

def vec_op_empty[A, B, C, D](x0: vec_ops_ext[A, B, C, D]): A = x0 match {
  case vec_ops_exta(vec_op_alpha, vec_op_scope, vec_op_idx, vec_op_invar,
                     vec_op_empty, vec_op_update, vec_op_restr, more)
    => vec_op_empty
}

def assignments_impl_vec_ops_uu_set_ops_api_input_doms_uu(api_input:
                    api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
                   x: nat):
      List[(Array.T[nat], nat)]
  =
  assignments_impl_aux_vec_ops_uu_api_input_doms_uu(api_input,
             g_to_sorted_list_bs_basic_ops(x),
             vec_op_empty[(Array.T[nat], nat), nat, nat,
                           Unit](vec_ops_uua(api_input)))

def scoped_fn_op_alpha[A, B, C, D,
                        E](x0: scoped_fn_basic_ops_ext[A, B, C, D, E]):
      A => B => C
  =
  x0 match {
  case scoped_fn_basic_ops_exta(scoped_fn_op_alpha, scoped_fn_op_scope_alpha,
                                 scoped_fn_op_scope, scoped_fn_op_from_fn,
                                 scoped_fn_op_invar, scoped_fn_op_inst,
                                 scoped_fn_op_eval, more)
    => scoped_fn_op_alpha
}

def scoped_fn_op_scope[A, B, C, D,
                        E](x0: scoped_fn_basic_ops_ext[A, B, C, D, E]):
      A => D
  =
  x0 match {
  case scoped_fn_basic_ops_exta(scoped_fn_op_alpha, scoped_fn_op_scope_alpha,
                                 scoped_fn_op_scope, scoped_fn_op_from_fn,
                                 scoped_fn_op_invar, scoped_fn_op_inst,
                                 scoped_fn_op_eval, more)
    => scoped_fn_op_scope
}

def eval_list_vec_ops_uu_api_input_doms_uu[A](api_input:
        api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
       f: ((Array.T[nat], nat)) => A, x: (Array.T[nat], nat), xa3: List[nat]):
      Scoped_Tree[A]
  =
  (api_input, f, x, xa3) match {
  case (api_input, f, x, Nil) => Scoped_Leaf[A](f(x))
  case (api_input, f, x, i :: is) =>
    Scoped_Node[A](i, Array.init_list[Scoped_Tree[A]](map[nat,
                   Scoped_Tree[A]](((z: nat) =>
                                     eval_list_vec_ops_uu_api_input_doms_uu[A](api_input,
f, (vec_op_update[(Array.T[nat], nat), nat, nat,
                   Unit](vec_ops_uua(api_input))).apply(x).apply(i).apply(z),
is)),
                                    upt.apply(zero_nata).apply((api_input_doms[nat,
(DiffArray.T[Option[real]], nat), Unit](api_input)).apply(i)))))
}

def vec_op_idx[A, B, C, D](x0: vec_ops_ext[A, B, C, D]): A => nat => B = x0
  match {
  case vec_ops_exta(vec_op_alpha, vec_op_scope, vec_op_idx, vec_op_invar,
                     vec_op_empty, vec_op_update, vec_op_restr, more)
    => vec_op_idx
}

def scoped_base_apply_vec_ops_uua(api_input:
                                    api_input_ext[nat,
           (DiffArray.T[Option[real]], nat), Unit],
                                   x1: Scoped_Tree[ereal],
                                   v: (Array.T[nat], nat)):
      ereal
  =
  (api_input, x1, v) match {
  case (api_input, Scoped_Leaf(y), v) => y
  case (api_input, Scoped_Node(i, arr), v) =>
    {
      val j =
        (vec_op_idx[(Array.T[nat], nat), nat, nat,
                     Unit](vec_ops_uua(api_input))).apply(v).apply(i):
          nat
      val true = less_nat(j, length[Scoped_Tree[ereal]](arr)): Boolean;
      scoped_base_apply_vec_ops_uua(api_input, sub[Scoped_Tree[ereal]](arr, j),
                                     v)
    }
}

def g_to_list_bs_basic_ops(s: nat): List[nat] =
  (iteratei_bset_op_list_it_bs_basic_ops[List[nat]](s)).apply(((_: List[nat]) =>
                        true)).apply(((a: nat) => (b: List[nat]) =>
                                       a :: b)).apply(Nil)

def scoped_eval_vec_ops_uu_set_ops_api_input_doms_uua(api_input:
                api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
               sf: (((Array.T[nat], nat)) => ereal, nat)):
      (((Array.T[nat], nat)) => ereal, nat)
  =
  {
    val (f, s) = sf: ((((Array.T[nat], nat)) => ereal, nat))
    val arr =
      eval_list_vec_ops_uu_api_input_doms_uu[ereal](api_input, f,
             vec_op_empty[(Array.T[nat], nat), nat, nat,
                           Unit](vec_ops_uua(api_input)),
             g_to_list_bs_basic_ops(s)):
        (Scoped_Tree[ereal])
    val fa =
      ((a: (Array.T[nat], nat)) =>
        scoped_base_apply_vec_ops_uua(api_input, arr, a)):
        (((Array.T[nat], nat)) => ereal);
    (fa, s)
  }

def scoped_invar_vec_ops_uu_set_opsb[A](a:
  api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
 b: (((Array.T[nat], nat)) => A, nat)):
      Boolean
  =
  sys.error("Code_Export.scoped_invar_vec_ops_uu_set_opsb")

def iteratei_set_op_list_it_set_ops[A](s: nat):
      (A => Boolean) => (nat => A => A) => A => A
  =
  bs_iteratei[A](s)

def vec_inst_vec_ops_uu_set_ops(api_input:
                                  api_input_ext[nat,
         (DiffArray.T[Option[real]], nat), Unit],
                                 va: (Array.T[nat], nat),
                                 v: (Array.T[nat], nat), s: nat):
      (Array.T[nat], nat)
  =
  (iteratei_set_op_list_it_set_ops[(Array.T[nat],
                                     nat)](s)).apply(((_: (Array.T[nat], nat))
                =>
               true)).apply(((i: nat) => (vb: (Array.T[nat], nat)) =>
                              (vec_op_update[(Array.T[nat], nat), nat, nat,
      Unit](vec_ops_uua(api_input))).apply(vb).apply(i).apply((vec_op_idx[(Array.T[nat],
                                    nat),
                                   nat, nat,
                                   Unit](vec_ops_uua(api_input))).apply(va).apply(i)))).apply(v)

def vec_op_scope[A, B, C, D](x0: vec_ops_ext[A, B, C, D]): A => C = x0 match {
  case vec_ops_exta(vec_op_alpha, vec_op_scope, vec_op_idx, vec_op_invar,
                     vec_op_empty, vec_op_update, vec_op_restr, more)
    => vec_op_scope
}

def unset_bit_nat(n: nat, m: nat): nat =
  (if (equal_nata(n, zero_nata))
    times_nata(nat_of_integer(BigInt(2)),
                divide_nata(m, nat_of_integer(BigInt(2))))
    else plus_nata(modulo_nata(m, nat_of_integer(BigInt(2))),
                    times_nata(nat_of_integer(BigInt(2)),
                                unset_bit_nat(minus_nata(n, one_nata),
       divide_nata(m, nat_of_integer(BigInt(2)))))))

def g_diff_bs_basic_ops(s1: nat, s2: nat): nat =
  (iteratei_bset_op_list_it_bs_basic_ops[nat](s2)).apply(((_: nat) =>
                   true)).apply(((a: nat) => (b: nat) =>
                                  unset_bit_nat(a, b))).apply(s1)

def scoped_scope[A, B, C](f: (A => B, C)): C = snd[A => B, C](f)

def scoped_inst_vec_ops_uu_set_opsb[A](api_input:
 api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
f: (((Array.T[nat], nat)) => A, nat), v: (Array.T[nat], nat)):
      (((Array.T[nat], nat)) => A, nat)
  =
  ({
     val s =
       g_inter_bs_basic_ops((vec_op_scope[(Array.T[nat], nat), nat, nat,
   Unit](vec_ops_uua(api_input))).apply(v),
                             scoped_scope[(Array.T[nat], nat), A, nat](f)):
         nat;
     ((va: (Array.T[nat], nat)) =>
       (fst[((Array.T[nat], nat)) => A,
             nat](f)).apply(vec_inst_vec_ops_uu_set_ops(api_input, v, va, s)))
   },
    g_diff_bs_basic_ops(scoped_scope[(Array.T[nat], nat), A, nat](f),
                         (vec_op_scope[(Array.T[nat], nat), nat, nat,
Unit](vec_ops_uua(api_input))).apply(v)))

def scoped_from_fn[A, B, C](s: A, f: B => C): (B => C, A) = (f, s)

def scoped_apply[A, B, C](f: (A => B, C), v: A): B =
  (fst[A => B, C](f)).apply(v)

def bs_alpha(a: nat): set[nat] = sys.error("Set_Inst.bs_\\<alpha>")

def scoped_fn_ops_vec_ops_uu_set_ops_api_input_doms_uua(api_input:
                  api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit]):
      scoped_fn_basic_ops_ext[(((Array.T[nat], nat)) => ereal, nat),
                               (Array.T[nat], nat), ereal, nat, Unit]
  =
  scoped_fn_basic_ops_exta[(((Array.T[nat], nat)) => ereal, nat),
                            (Array.T[nat], nat), ereal, nat,
                            Unit](((a: (((Array.T[nat], nat)) => ereal, nat)) =>
                                    (b: (Array.T[nat], nat)) =>
                                    scoped_apply[(Array.T[nat], nat), ereal,
          nat](a, b)),
                                   ((f: (((Array.T[nat], nat)) => ereal, nat))
                                      =>
                                     bs_alpha(scoped_scope[(Array.T[nat], nat),
                    ereal, nat](f))),
                                   ((a: (((Array.T[nat], nat)) => ereal, nat))
                                      =>
                                     scoped_scope[(Array.T[nat], nat), ereal,
           nat](a)),
                                   ((a: nat) =>
                                     (b: ((Array.T[nat], nat)) => ereal) =>
                                     scoped_from_fn[nat, (Array.T[nat], nat),
             ereal](a, b)),
                                   ((a: (((Array.T[nat], nat)) => ereal, nat))
                                      =>
                                     scoped_invar_vec_ops_uu_set_opsb[ereal](api_input,
                                      a)),
                                   ((a: (((Array.T[nat], nat)) => ereal, nat))
                                      =>
                                     (b: (Array.T[nat], nat)) =>
                                     scoped_inst_vec_ops_uu_set_opsb[ereal](api_input,
                                     a, b)),
                                   ((a: (((Array.T[nat], nat)) => ereal, nat))
                                      =>
                                     scoped_eval_vec_ops_uu_set_ops_api_input_doms_uua(api_input,
        a)),
                                   ())

def scoped_ind_vec_ops_uu_set_ops_api_input_doms_uu(api_input:
              api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
             v: (Array.T[nat], nat)):
      (((Array.T[nat], nat)) => ereal, nat)
  =
  scoped_eval_vec_ops_uu_set_ops_api_input_doms_uua(api_input,
             (((va: (Array.T[nat], nat)) =>
                (if (g_ball_bs_basic_ops((vec_op_scope[(Array.T[nat], nat), nat,
                nat, Unit](vec_ops_uua(api_input))).apply(v),
  ((i: nat) =>
    equal_nata((vec_op_idx[(Array.T[nat], nat), nat, nat,
                            Unit](vec_ops_uua(api_input))).apply(v).apply(i),
                (vec_op_idx[(Array.T[nat], nat), nat, nat,
                             Unit](vec_ops_uua(api_input))).apply(va).apply(i)))))
                  MInfty() else zero_ereala)),
               (vec_op_scope[(Array.T[nat], nat), nat, nat,
                              Unit](vec_ops_uua(api_input))).apply(v)))

def scoped_fn_op_scope_alpha[A, B, C, D,
                              E](x0: scoped_fn_basic_ops_ext[A, B, C, D, E]):
      A => set[nat]
  =
  x0 match {
  case scoped_fn_basic_ops_exta(scoped_fn_op_alpha, scoped_fn_op_scope_alpha,
                                 scoped_fn_op_scope, scoped_fn_op_from_fn,
                                 scoped_fn_op_invar, scoped_fn_op_inst,
                                 scoped_fn_op_eval, more)
    => scoped_fn_op_scope_alpha
}

def scoped_fn_op_from_fn[A, B, C, D,
                          E](x0: scoped_fn_basic_ops_ext[A, B, C, D, E]):
      D => (B => C) => A
  =
  x0 match {
  case scoped_fn_basic_ops_exta(scoped_fn_op_alpha, scoped_fn_op_scope_alpha,
                                 scoped_fn_op_scope, scoped_fn_op_from_fn,
                                 scoped_fn_op_invar, scoped_fn_op_inst,
                                 scoped_fn_op_eval, more)
    => scoped_fn_op_from_fn
}

def scoped_fn_op_invar[A, B, C, D,
                        E](x0: scoped_fn_basic_ops_ext[A, B, C, D, E]):
      A => Boolean
  =
  x0 match {
  case scoped_fn_basic_ops_exta(scoped_fn_op_alpha, scoped_fn_op_scope_alpha,
                                 scoped_fn_op_scope, scoped_fn_op_from_fn,
                                 scoped_fn_op_invar, scoped_fn_op_inst,
                                 scoped_fn_op_eval, more)
    => scoped_fn_op_invar
}

def scoped_fn_op_inst[A, B, C, D,
                       E](x0: scoped_fn_basic_ops_ext[A, B, C, D, E]):
      A => B => A
  =
  x0 match {
  case scoped_fn_basic_ops_exta(scoped_fn_op_alpha, scoped_fn_op_scope_alpha,
                                 scoped_fn_op_scope, scoped_fn_op_from_fn,
                                 scoped_fn_op_invar, scoped_fn_op_inst,
                                 scoped_fn_op_eval, more)
    => scoped_fn_op_inst
}

def scoped_fn_op_eval[A, B, C, D,
                       E](x0: scoped_fn_basic_ops_ext[A, B, C, D, E]):
      A => A
  =
  x0 match {
  case scoped_fn_basic_ops_exta(scoped_fn_op_alpha, scoped_fn_op_scope_alpha,
                                 scoped_fn_op_scope, scoped_fn_op_from_fn,
                                 scoped_fn_op_invar, scoped_fn_op_inst,
                                 scoped_fn_op_eval, more)
    => scoped_fn_op_eval
}

def extend[A, B, C, D,
            E](r: scoped_fn_basic_ops_ext[A, B, C, D, Unit], more: E):
      scoped_fn_basic_ops_ext[A, B, C, D, E]
  =
  scoped_fn_basic_ops_exta[A, B, C, D,
                            E](scoped_fn_op_alpha[A, B, C, D, Unit](r),
                                scoped_fn_op_scope_alpha[A, B, C, D, Unit](r),
                                scoped_fn_op_scope[A, B, C, D, Unit](r),
                                scoped_fn_op_from_fn[A, B, C, D, Unit](r),
                                scoped_fn_op_invar[A, B, C, D, Unit](r),
                                scoped_fn_op_inst[A, B, C, D, Unit](r),
                                scoped_fn_op_eval[A, B, C, D, Unit](r), more)

def scoped_ereal_ops_uua(api_input:
                           api_input_ext[nat, (DiffArray.T[Option[real]], nat),
  Unit]):
      scoped_fn_basic_ops_ext[(((Array.T[nat], nat)) => ereal, nat),
                               (Array.T[nat], nat), ereal, nat,
                               scoped_fn_ereal_ops_ext[(((Array.T[nat], nat)) =>
                  ereal,
                 nat),
                (Array.T[nat], nat), Unit]]
  =
  extend[(((Array.T[nat], nat)) => ereal, nat), (Array.T[nat], nat), ereal, nat,
          scoped_fn_ereal_ops_ext[(((Array.T[nat], nat)) => ereal, nat),
                                   (Array.T[nat], nat),
                                   Unit]](scoped_fn_ops_vec_ops_uu_set_ops_api_input_doms_uua(api_input),
   scoped_fn_ereal_ops_exta[(Array.T[nat], nat),
                             (((Array.T[nat], nat)) => ereal, nat),
                             Unit](((a: (Array.T[nat], nat)) =>
                                     scoped_ind_vec_ops_uu_set_ops_api_input_doms_uu(api_input,
      a)),
                                    ()))

def real_of_ereal(x0: ereal): real = x0 match {
  case ereala(r) => r
  case PInfty() => zero_reala
  case MInfty() => zero_reala
}

def constrs_b_single_code_vec_ops_uu_set_ops_api_input_doms_uu_scoped_ereal_ops_uu_constr_map_ops_Pair_show_state_vec_ops_uu_api_input_dims_uu_uu_Pair_uu_uu_show_state_vec_ops_uu_api_input_dims_uu(api_input:
                                       api_input_ext[nat,
              (DiffArray.T[Option[real]], nat), Unit],
                                      t_code: (Array.T[nat], nat), a_code: nat,
                                      pos: Boolean, i: nat,
                                      b: (((Array.T[nat], nat)) => ereal, nat)):
      List[Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
 List[Option[nat]]],
                                real]]]
  =
  map_filter[(Array.T[nat], nat),
              Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
    List[Option[nat]]],
                                   real]]](((z: (Array.T[nat], nat)) =>
     {
       val rhs =
         (scoped_fn_op_alpha[(((Array.T[nat], nat)) => ereal, nat),
                              (Array.T[nat], nat), ereal, nat,
                              scoped_fn_ereal_ops_ext[(((Array.T[nat], nat)) =>
                 ereal,
                nat),
               (Array.T[nat], nat),
               Unit]](scoped_ereal_ops_uua(api_input))).apply(b).apply(z):
           ereal;
       (if (equal_ereal(rhs, MInfty())) None
         else Some[Constr_Code[hashmap[var_code[(List[Option[nat]],
          (nat, Boolean)),
         List[Option[nat]]],
real]]](constr_b_code_constr_map_ops_Pair_show_state_vec_ops_uu_api_input_dims_uu_uu_Pair_uu_uu_show_state_vec_ops_uu_api_input_dims_uu(api_input,
                 t_code, a_code, pos, z, i, real_of_ereal(rhs))))
     }),
    assignments_impl_vec_ops_uu_set_ops_api_input_doms_uu(api_input,
                   (scoped_fn_op_scope[(((Array.T[nat], nat)) => ereal, nat),
(Array.T[nat], nat), ereal, nat,
scoped_fn_ereal_ops_ext[(((Array.T[nat], nat)) => ereal, nat),
                         (Array.T[nat], nat),
                         Unit]](scoped_ereal_ops_uua(api_input))).apply(b)))

def constrs_b_code_vec_ops_uu_set_ops_api_input_doms_uu_scoped_ereal_ops_uu_constr_map_ops_uu_Pair_show_state_vec_ops_uu_api_input_dims_uu_uu_Pair_uu_uu_show_state_vec_ops_uu_api_input_dims_uu(api_input:
                                   api_input_ext[nat,
          (DiffArray.T[Option[real]], nat), Unit],
                                  b_code:
                                    List[(((Array.T[nat], nat)) => ereal, nat)],
                                  t_code: (Array.T[nat], nat), a_code: nat,
                                  pos: Boolean):
      List[Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
 List[Option[nat]]],
                                real]]]
  =
  maps[(nat, (((Array.T[nat], nat)) => ereal, nat)),
        Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                                      List[Option[nat]]],
                             real]]](((a:
 (nat, (((Array.T[nat], nat)) => ereal, nat)))
=>
                                       {
 val (aa, b) = a: ((nat, (((Array.T[nat], nat)) => ereal, nat)));
 constrs_b_single_code_vec_ops_uu_set_ops_api_input_doms_uu_scoped_ereal_ops_uu_constr_map_ops_Pair_show_state_vec_ops_uu_api_input_dims_uu_uu_Pair_uu_uu_show_state_vec_ops_uu_api_input_dims_uu(api_input,
                                   t_code, a_code, pos, aa, b)
                                       }),
                                      enumerate[(((Array.T[nat], nat)) => ereal,
          nat)](zero_nata, b_code))

def scoped_base_apply_vec_ops_uu(api_input:
                                   api_input_ext[nat,
          (DiffArray.T[Option[real]], nat), Unit],
                                  x1: Scoped_Tree[real],
                                  v: (Array.T[nat], nat)):
      real
  =
  (api_input, x1, v) match {
  case (api_input, Scoped_Leaf(y), v) => y
  case (api_input, Scoped_Node(i, arr), v) =>
    {
      val j =
        (vec_op_idx[(Array.T[nat], nat), nat, nat,
                     Unit](vec_ops_uua(api_input))).apply(v).apply(i):
          nat
      val true = less_nat(j, length[Scoped_Tree[real]](arr)): Boolean;
      scoped_base_apply_vec_ops_uu(api_input, sub[Scoped_Tree[real]](arr, j), v)
    }
}

def scoped_eval_vec_ops_uu_set_ops_api_input_doms_uu(api_input:
               api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
              sf: (((Array.T[nat], nat)) => real, nat)):
      (((Array.T[nat], nat)) => real, nat)
  =
  {
    val (f, s) = sf: ((((Array.T[nat], nat)) => real, nat))
    val arr =
      eval_list_vec_ops_uu_api_input_doms_uu[real](api_input, f,
            vec_op_empty[(Array.T[nat], nat), nat, nat,
                          Unit](vec_ops_uua(api_input)),
            g_to_list_bs_basic_ops(s)):
        (Scoped_Tree[real])
    val fa =
      ((a: (Array.T[nat], nat)) =>
        scoped_base_apply_vec_ops_uu(api_input, arr, a)):
        (((Array.T[nat], nat)) => real);
    (fa, s)
  }

def scoped_fn_ops_vec_ops_uu_set_ops_api_input_doms_uu(api_input:
                 api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit]):
      scoped_fn_basic_ops_ext[(((Array.T[nat], nat)) => real, nat),
                               (Array.T[nat], nat), real, nat, Unit]
  =
  scoped_fn_basic_ops_exta[(((Array.T[nat], nat)) => real, nat),
                            (Array.T[nat], nat), real, nat,
                            Unit](((a: (((Array.T[nat], nat)) => real, nat)) =>
                                    (b: (Array.T[nat], nat)) =>
                                    scoped_apply[(Array.T[nat], nat), real,
          nat](a, b)),
                                   ((f: (((Array.T[nat], nat)) => real, nat)) =>
                                     bs_alpha(scoped_scope[(Array.T[nat], nat),
                    real, nat](f))),
                                   ((a: (((Array.T[nat], nat)) => real, nat)) =>
                                     scoped_scope[(Array.T[nat], nat), real,
           nat](a)),
                                   ((a: nat) =>
                                     (b: ((Array.T[nat], nat)) => real) =>
                                     scoped_from_fn[nat, (Array.T[nat], nat),
             real](a, b)),
                                   ((a: (((Array.T[nat], nat)) => real, nat)) =>
                                     scoped_invar_vec_ops_uu_set_opsb[real](api_input,
                                     a)),
                                   ((a: (((Array.T[nat], nat)) => real, nat)) =>
                                     (b: (Array.T[nat], nat)) =>
                                     scoped_inst_vec_ops_uu_set_opsb[real](api_input,
                                    a, b)),
                                   ((a: (((Array.T[nat], nat)) => real, nat)) =>
                                     scoped_eval_vec_ops_uu_set_ops_api_input_doms_uu(api_input,
       a)),
                                   ())

def minus_fun[A, B : minus](a: A => B, b: A => B, x: A): B =
  minus[B](a(x), b(x))

def g_union_bs_basic_ops(s1: nat, s2: nat): nat =
  (iteratei_bset_op_list_it_bs_basic_ops[nat](s1)).apply(((_: nat) =>
                   true)).apply(((a: nat) => (b: nat) =>
                                  set_bit_nat(a, b))).apply(s2)

def scoped_diff_set_ops(f1: (((Array.T[nat], nat)) => real, nat),
                         f2: (((Array.T[nat], nat)) => real, nat)):
      (((Array.T[nat], nat)) => real, nat)
  =
  (((a: (Array.T[nat], nat)) =>
     minus_fun[(Array.T[nat], nat),
                real](fst[((Array.T[nat], nat)) => real, nat](f1),
                       fst[((Array.T[nat], nat)) => real, nat](f2), a)),
    g_union_bs_basic_ops(scoped_scope[(Array.T[nat], nat), real, nat](f1),
                          scoped_scope[(Array.T[nat], nat), real, nat](f2)))

def scoped_scale[A, B : times, C](f: (A => B, C), c: B): (A => B, C) =
  (((v: A) => times[B]((fst[A => B, C](f)).apply(v), c)), snd[A => B, C](f))

def scoped_real_ops_uua(api_input:
                          api_input_ext[nat, (DiffArray.T[Option[real]], nat),
 Unit]):
      scoped_fn_basic_ops_ext[(((Array.T[nat], nat)) => real, nat),
                               (Array.T[nat], nat), real, nat,
                               scoped_fn_real_ops_ext[(((Array.T[nat], nat)) =>
                 real,
                nat),
               Unit]]
  =
  extend[(((Array.T[nat], nat)) => real, nat), (Array.T[nat], nat), real, nat,
          scoped_fn_real_ops_ext[(((Array.T[nat], nat)) => real, nat),
                                  Unit]](scoped_fn_ops_vec_ops_uu_set_ops_api_input_doms_uu(api_input),
  scoped_fn_real_ops_exta[(((Array.T[nat], nat)) => real, nat),
                           Unit](((a: (((Array.T[nat], nat)) => real, nat)) =>
                                   (b: real) =>
                                   scoped_scale[(Array.T[nat], nat), real,
         nat](a, b)),
                                  ((a: (((Array.T[nat], nat)) => real, nat)) =>
                                    (b: (((Array.T[nat], nat)) => real, nat)) =>
                                    scoped_diff_set_ops(a, b)),
                                  ()))

def constr_c_code_scoped_real_ops_uu_constr_map_ops_Pair_show_state_vec_ops_uu_api_input_dims_uu_uu_Pair_uu_uu_show_state_vec_ops_uu_api_input_dims_uu(api_input:
                                 api_input_ext[nat,
        (DiffArray.T[Option[real]], nat), Unit],
                                t_code: (Array.T[nat], nat), a_code: nat,
                                pos: Boolean, z: (Array.T[nat], nat), i: nat,
                                c: (((Array.T[nat], nat)) => real, nat)):
      Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                                    List[Option[nat]]],
                           real]]
  =
  {
    val var_c =
      var_f[(List[Option[nat]], (nat, Boolean)),
             List[Option[nat]]]((show_state_vec_ops_uu_api_input_dims_uu(api_input,
                                  t_code),
                                  (a_code, pos)),
                                 f_c_code(i),
                                 show_state_vec_ops_uu_api_input_dims_uu(api_input,
                                  z)):
        (var_code[(List[Option[nat]], (nat, Boolean)), List[Option[nat]]]);
    constr_eq_from_list_constr_map_ops(List((var_c, uminus_reala(one_reala)),
     (var_w[(List[Option[nat]], (nat, Boolean)), List[Option[nat]]](i),
       (scoped_fn_op_alpha[(((Array.T[nat], nat)) => real, nat),
                            (Array.T[nat], nat), real, nat,
                            scoped_fn_real_ops_ext[(((Array.T[nat], nat)) =>
              real,
             nat),
            Unit]](scoped_real_ops_uua(api_input))).apply(c).apply(z))),
zero_reala)
  }

def constrs_c_single_code_vec_ops_uu_set_ops_api_input_doms_uu_scoped_real_ops_uu_constr_map_ops_Pair_show_state_vec_ops_uu_api_input_dims_uu_uu_Pair_uu_uu_show_state_vec_ops_uu_api_input_dims_uu(api_input:
                                      api_input_ext[nat,
             (DiffArray.T[Option[real]], nat), Unit],
                                     t_code: (Array.T[nat], nat), a_code: nat,
                                     pos: Boolean, i: nat,
                                     c: (((Array.T[nat], nat)) => real, nat)):
      List[Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
 List[Option[nat]]],
                                real]]]
  =
  map[(Array.T[nat], nat),
       Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                                     List[Option[nat]]],
                            real]]](((z: (Array.T[nat], nat)) =>
                                      constr_c_code_scoped_real_ops_uu_constr_map_ops_Pair_show_state_vec_ops_uu_api_input_dims_uu_uu_Pair_uu_uu_show_state_vec_ops_uu_api_input_dims_uu(api_input,
                          t_code, a_code, pos, z, i, c)),
                                     assignments_impl_vec_ops_uu_set_ops_api_input_doms_uu(api_input,
            (scoped_fn_op_scope[(((Array.T[nat], nat)) => real, nat),
                                 (Array.T[nat], nat), real, nat,
                                 scoped_fn_real_ops_ext[(((Array.T[nat],
                   nat)) =>
                   real,
                  nat),
                 Unit]](scoped_real_ops_uua(api_input))).apply(c)))

def constrs_c_code_vec_ops_uu_set_ops_api_input_doms_uu_scoped_real_ops_uu_constr_map_ops_uu_Pair_show_state_vec_ops_uu_api_input_dims_uu_uu_Pair_uu_uu_show_state_vec_ops_uu_api_input_dims_uu(api_input:
                                  api_input_ext[nat,
         (DiffArray.T[Option[real]], nat), Unit],
                                 c_code:
                                   List[(((Array.T[nat], nat)) => real, nat)],
                                 t_code: (Array.T[nat], nat), a_code: nat,
                                 pos: Boolean):
      List[Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
 List[Option[nat]]],
                                real]]]
  =
  maps[(nat, (((Array.T[nat], nat)) => real, nat)),
        Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                                      List[Option[nat]]],
                             real]]](((a:
 (nat, (((Array.T[nat], nat)) => real, nat)))
=>
                                       {
 val (aa, b) = a: ((nat, (((Array.T[nat], nat)) => real, nat)));
 constrs_c_single_code_vec_ops_uu_set_ops_api_input_doms_uu_scoped_real_ops_uu_constr_map_ops_Pair_show_state_vec_ops_uu_api_input_dims_uu_uu_Pair_uu_uu_show_state_vec_ops_uu_api_input_dims_uu(api_input,
                                  t_code, a_code, pos, aa, b)
                                       }),
                                      enumerate[(((Array.T[nat], nat)) => real,
          nat)](zero_nata, c_code))

def constrs_init_code_vec_ops_uu_set_ops_api_input_doms_uu_scoped_ereal_ops_uu_scoped_real_ops_uu_constr_map_ops_uu_uu_Pair_show_state_vec_ops_uu_api_input_dims_uu_uu_Pair_uu_uu_show_state_vec_ops_uu_api_input_dims_uu(api_input:
                    api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
                   c_code: List[(((Array.T[nat], nat)) => real, nat)],
                   b_code: List[(((Array.T[nat], nat)) => ereal, nat)],
                   t_code: (Array.T[nat], nat), a_code: nat, pos: Boolean):
      List[Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
 List[Option[nat]]],
                                real]]]
  =
  constrs_c_code_vec_ops_uu_set_ops_api_input_doms_uu_scoped_real_ops_uu_constr_map_ops_uu_Pair_show_state_vec_ops_uu_api_input_dims_uu_uu_Pair_uu_uu_show_state_vec_ops_uu_api_input_dims_uu(api_input,
                               c_code, t_code, a_code, pos) ++
    constrs_b_code_vec_ops_uu_set_ops_api_input_doms_uu_scoped_ereal_ops_uu_constr_map_ops_uu_Pair_show_state_vec_ops_uu_api_input_dims_uu_uu_Pair_uu_uu_show_state_vec_ops_uu_api_input_dims_uu(api_input,
                                  b_code, t_code, a_code, pos)

def constr_le_from_list_constr_map_ops(xs:
 List[(var_code[(List[Option[nat]], (nat, Boolean)), List[Option[nat]]], real)],
rhs: real):
      Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                                    List[Option[nat]]],
                           real]]
  =
  Constr_Le[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                              List[Option[nat]]],
                     real]](g_list_to_map_ahm_basic_ops[var_code[(List[Option[nat]],
                           (nat, Boolean)),
                          List[Option[nat]]],
                 real](xs),
                             rhs)

def vec_from_idx_vec_ops_uu_set_ops(api_input:
                                      api_input_ext[nat,
             (DiffArray.T[Option[real]], nat), Unit],
                                     x: nat, f: nat => nat):
      (Array.T[nat], nat)
  =
  (iteratei_set_op_list_it_set_ops[(Array.T[nat],
                                     nat)](x)).apply(((_: (Array.T[nat], nat))
                =>
               true)).apply(((j: nat) => (v: (Array.T[nat], nat)) =>
                              (vec_op_update[(Array.T[nat], nat), nat, nat,
      Unit](vec_ops_uua(api_input))).apply(v).apply(j).apply(f(j)))).apply(vec_op_empty[(Array.T[nat],
          nat),
         nat, nat, Unit](vec_ops_uua(api_input)))

def constr_max_code_vec_ops_uu_set_ops_constr_map_ops_Pair_show_state_vec_ops_uu_api_input_dims_uu_uu_Pair_uu_uu_show_state_vec_ops_uu_api_input_dims_uu(api_input:
                                   api_input_ext[nat,
          (DiffArray.T[Option[real]], nat), Unit],
                                  t_code: (Array.T[nat], nat), a_code: nat,
                                  pos: Boolean, e: List[(f_name_code, nat)],
                                  i: nat, z: (Array.T[nat], nat), xi: nat):
      Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                                    List[Option[nat]]],
                           real]]
  =
  constr_le_from_list_constr_map_ops((var_f[(List[Option[nat]], (nat, Boolean)),
     List[Option[nat]]]((show_state_vec_ops_uu_api_input_dims_uu(api_input,
                          t_code),
                          (a_code, pos)),
                         f_e_code(i),
                         show_state_vec_ops_uu_api_input_dims_uu(api_input, z)),
                                       uminus_reala(one_reala)) ::
                                       map[(f_name_code, nat),
    (var_code[(List[Option[nat]], (nat, Boolean)), List[Option[nat]]],
      real)](((a: (f_name_code, nat)) =>
               {
                 val (f, s) = a: ((f_name_code, nat));
                 (var_f[(List[Option[nat]], (nat, Boolean)),
                         List[Option[nat]]]((show_state_vec_ops_uu_api_input_dims_uu(api_input,
      t_code),
      (a_code, pos)),
     f, show_state_vec_ops_uu_api_input_dims_uu(api_input,
         vec_from_idx_vec_ops_uu_set_ops(api_input, s,
  ((j: nat) =>
    (if (equal_nata(j, i)) xi
      else (vec_op_idx[(Array.T[nat], nat), nat, nat,
                        Unit](vec_ops_uua(api_input))).apply(z).apply(j)))))),
                   one_reala)
               }),
              e),
                                      zero_reala)

def constrs_max_code_vec_ops_uu_set_ops_api_input_doms_uu_constr_map_ops_Pair_show_state_vec_ops_uu_api_input_dims_uu_uu_Pair_uu_uu_show_state_vec_ops_uu_api_input_dims_uu(api_input:
              api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
             t_code: (Array.T[nat], nat), a_code: nat, pos: Boolean,
             e: List[(f_name_code, nat)], i: nat, scope_e: nat):
      List[Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
 List[Option[nat]]],
                                real]]]
  =
  map[((Array.T[nat], nat), nat),
       Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                                     List[Option[nat]]],
                            real]]](((a: ((Array.T[nat], nat), nat)) =>
                                      {
val (aa, b) = a: (((Array.T[nat], nat), nat));
constr_max_code_vec_ops_uu_set_ops_constr_map_ops_Pair_show_state_vec_ops_uu_api_input_dims_uu_uu_Pair_uu_uu_show_state_vec_ops_uu_api_input_dims_uu(api_input,
                              t_code, a_code, pos, e, i, aa, b)
                                      }),
                                     product[(Array.T[nat], nat),
      nat](assignments_impl_vec_ops_uu_set_ops_api_input_doms_uu(api_input,
                          scope_e),
            upt.apply(zero_nata).apply((api_input_doms[nat,
                (DiffArray.T[Option[real]], nat), Unit](api_input)).apply(i))))

def Union_sets_set_ops(x: List[nat]): nat =
  fold[nat, nat](((a: nat) => (b: nat) => g_union_bs_basic_ops(a, b)), x,
                  zero_nata)

def elim_step_code_vec_ops_uu_set_ops_api_input_doms_uu_constr_map_ops_Pair_show_state_vec_ops_uu_api_input_dims_uu_uu_Pair_uu_uu_show_state_vec_ops_uu_api_input_dims_uu(api_input:
            api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
           t_code: (Array.T[nat], nat), a_code: nat, pos: Boolean,
           omega:
             List[Constr_Code[hashmap[var_code[(List[Option[nat]],
         (nat, Boolean)),
        List[Option[nat]]],
                                       real]]],
           f: List[(f_name_code, nat)], i: nat):
      (List[Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
  List[Option[nat]]],
                                 real]]],
        (List[(f_name_code, nat)], nat))
  =
  {
    val l = i: nat
    val (e, not_E) =
      partition[(f_name_code,
                  nat)](((a: (f_name_code, nat)) =>
                          {
                            val (_, s) = a: ((f_name_code, nat));
                            bit_nat(s, l)
                          }),
                         f):
        ((List[(f_name_code, nat)], List[(f_name_code, nat)]))
    val scope_e =
      unset_bit_nat(l, Union_sets_set_ops(map[(f_name_code, nat),
       nat](((a: (f_name_code, nat)) => snd[f_name_code, nat](a)), e))):
        nat
    val omegaa =
      omega ++
        constrs_max_code_vec_ops_uu_set_ops_api_input_doms_uu_constr_map_ops_Pair_show_state_vec_ops_uu_api_input_dims_uu_uu_Pair_uu_uu_show_state_vec_ops_uu_api_input_dims_uu(api_input,
                 t_code, a_code, pos, e, l, scope_e):
        (List[Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
    List[Option[nat]]],
                                   real]]]);
    (omegaa, ((f_e_code(l), scope_e) :: not_E, plus_nata(i, one_nata)))
  }

def F_init_code_scoped_ereal_ops_uu_scoped_real_ops_uu_uu_uu(api_input:
                       api_input_ext[nat, (DiffArray.T[Option[real]], nat),
                                      Unit],
                      c_code: List[(((Array.T[nat], nat)) => real, nat)],
                      b_code: List[(((Array.T[nat], nat)) => ereal, nat)]):
      List[(f_name_code, nat)]
  =
  map[(nat, (((Array.T[nat], nat)) => real, nat)),
       (f_name_code,
         nat)](((a: (nat, (((Array.T[nat], nat)) => real, nat))) =>
                 {
                   val (i, f) =
                     a: ((nat, (((Array.T[nat], nat)) => real, nat)));
                   (f_c_code(i),
                     (scoped_fn_op_scope[(((Array.T[nat], nat)) => real, nat),
  (Array.T[nat], nat), real, nat,
  scoped_fn_real_ops_ext[(((Array.T[nat], nat)) => real, nat),
                          Unit]](scoped_real_ops_uua(api_input))).apply(f))
                 }),
                enumerate[(((Array.T[nat], nat)) => real,
                            nat)](zero_nata, c_code)) ++
    map[(nat, (((Array.T[nat], nat)) => ereal, nat)),
         (f_name_code,
           nat)](((a: (nat, (((Array.T[nat], nat)) => ereal, nat))) =>
                   {
                     val (i, f) =
                       a: ((nat, (((Array.T[nat], nat)) => ereal, nat)));
                     (f_b_code(i),
                       (scoped_fn_op_scope[(((Array.T[nat], nat)) => ereal,
     nat),
    (Array.T[nat], nat), ereal, nat,
    scoped_fn_ereal_ops_ext[(((Array.T[nat], nat)) => ereal, nat),
                             (Array.T[nat], nat),
                             Unit]](scoped_ereal_ops_uua(api_input))).apply(f))
                   }),
                  enumerate[(((Array.T[nat], nat)) => ereal,
                              nat)](zero_nata, b_code))

def elim_vars_aux_code_vec_ops_uu_set_ops_api_input_dims_uu_api_input_doms_uu_scoped_ereal_ops_uu_scoped_real_ops_uu_constr_map_ops_uu_uu_Pair_show_state_vec_ops_uu_api_input_dims_uu_uu_Pair_uu_uu_show_state_vec_ops_uu_api_input_dims_uu(api_input:
                                       api_input_ext[nat,
              (DiffArray.T[Option[real]], nat), Unit],
                                      c_code:
List[(((Array.T[nat], nat)) => real, nat)],
                                      b_code:
List[(((Array.T[nat], nat)) => ereal, nat)],
                                      t_code: (Array.T[nat], nat), a_code: nat,
                                      pos: Boolean):
      (List[Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
  List[Option[nat]]],
                                 real]]],
        (List[(f_name_code, nat)], nat))
  =
  (funpow[(List[Constr_Code[hashmap[var_code[(List[Option[nat]],
       (nat, Boolean)),
      List[Option[nat]]],
                                     real]]],
            (List[(f_name_code, nat)],
              nat))](api_input_dims[nat, (DiffArray.T[Option[real]], nat),
                                     Unit](api_input),
                      ((a: (List[Constr_Code[hashmap[var_code[(List[Option[nat]],
                        (nat, Boolean)),
                       List[Option[nat]]],
              real]]],
                             (List[(f_name_code, nat)], nat)))
                         =>
                        {
                          val (omega, (aa, b)) =
                            a: ((List[Constr_Code[hashmap[var_code[(List[Option[nat]],
                             (nat, Boolean)),
                            List[Option[nat]]],
                   real]]],
                                 (List[(f_name_code, nat)], nat)));
                          elim_step_code_vec_ops_uu_set_ops_api_input_doms_uu_constr_map_ops_Pair_show_state_vec_ops_uu_api_input_dims_uu_uu_Pair_uu_uu_show_state_vec_ops_uu_api_input_dims_uu(api_input,
                                 t_code, a_code, pos, omega, aa, b)
                        }))).apply((constrs_init_code_vec_ops_uu_set_ops_api_input_doms_uu_scoped_ereal_ops_uu_scoped_real_ops_uu_constr_map_ops_uu_uu_Pair_show_state_vec_ops_uu_api_input_dims_uu_uu_Pair_uu_uu_show_state_vec_ops_uu_api_input_dims_uu(api_input,
           c_code, b_code, t_code, a_code, pos),
                                     (F_init_code_scoped_ereal_ops_uu_scoped_real_ops_uu_uu_uu(api_input,
                c_code, b_code),
                                       zero_nata)))

def gen_constrs_code_vec_ops_uu_constr_map_ops_Pair_show_state_vec_ops_uu_api_input_dims_uu_uu_Pair_uu_uu_show_state_vec_ops_uu_api_input_dims_uu[A,
                           B](api_input:
                                api_input_ext[nat,
       (DiffArray.T[Option[real]], nat), Unit],
                               t_code: (Array.T[nat], nat), a_code: nat,
                               pos: Boolean,
                               arg: (List[Constr_Code[hashmap[var_code[(List[Option[nat]],
                                 (nat, Boolean)),
                                List[Option[nat]]],
                       real]]],
                                      (List[(f_name_code, A)], B))):
      List[Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
 List[Option[nat]]],
                                real]]]
  =
  {
    val (omega, (f, _)) =
      arg: ((List[Constr_Code[hashmap[var_code[(List[Option[nat]],
         (nat, Boolean)),
        List[Option[nat]]],
                                       real]]],
             (List[(f_name_code, A)], B)));
    constr_le_from_list_constr_map_ops((var_phi[(List[Option[nat]],
          (nat, Boolean)),
         List[Option[nat]]](),
 uminus_reala(one_reala)) ::
 map[(f_name_code, A),
      (var_code[(List[Option[nat]], (nat, Boolean)), List[Option[nat]]],
        real)](((a: (f_name_code, A)) =>
                 {
                   val (fa, _) = a: ((f_name_code, A));
                   (var_f[(List[Option[nat]], (nat, Boolean)),
                           List[Option[nat]]]((show_state_vec_ops_uu_api_input_dims_uu(api_input,
        t_code),
        (a_code, pos)),
       fa, show_state_vec_ops_uu_api_input_dims_uu(api_input,
            vec_op_empty[(Array.T[nat], nat), nat, nat,
                          Unit](vec_ops_uua(api_input)))),
                     one_reala)
                 }),
                f),
zero_reala) ::
      omega
  }

def elim_vars_code_vec_ops_uu_set_ops_api_input_dims_uu_api_input_doms_uu_scoped_ereal_ops_uu_scoped_real_ops_uu_constr_map_ops_uu_uu_Pair_show_state_vec_ops_uu_api_input_dims_uu_uu_Pair_uu_uu_show_state_vec_ops_uu_api_input_dims_uu(api_input:
                                   api_input_ext[nat,
          (DiffArray.T[Option[real]], nat), Unit],
                                  c_code:
                                    List[(((Array.T[nat], nat)) => real, nat)],
                                  b_code:
                                    List[(((Array.T[nat], nat)) => ereal, nat)],
                                  t_code: (Array.T[nat], nat), a_code: nat,
                                  pos: Boolean):
      List[Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
 List[Option[nat]]],
                                real]]]
  =
  gen_constrs_code_vec_ops_uu_constr_map_ops_Pair_show_state_vec_ops_uu_api_input_dims_uu_uu_Pair_uu_uu_show_state_vec_ops_uu_api_input_dims_uu[nat,
                         nat](api_input, t_code, a_code, pos,
                               elim_vars_aux_code_vec_ops_uu_set_ops_api_input_dims_uu_api_input_doms_uu_scoped_ereal_ops_uu_scoped_real_ops_uu_constr_map_ops_uu_uu_Pair_show_state_vec_ops_uu_api_input_dims_uu_uu_Pair_uu_uu_show_state_vec_ops_uu_api_input_dims_uu(api_input,
                         c_code, b_code, t_code, a_code, pos))

def factored_lp_code_vec_ops_uu_set_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_scoped_real_ops_uu_scoped_ereal_ops_uu_constr_map_ops_uu_uu(api_input:
                                    api_input_ext[nat,
           (DiffArray.T[Option[real]], nat), Unit],
                                   t_code: (Array.T[nat], nat), a_code: nat,
                                   pos: Boolean,
                                   c: List[(((Array.T[nat], nat)) => real,
     nat)],
                                   b: List[(((Array.T[nat], nat)) => ereal,
     nat)]):
      List[Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
 List[Option[nat]]],
                                real]]]
  =
  elim_vars_code_vec_ops_uu_set_ops_api_input_dims_uu_api_input_doms_uu_scoped_ereal_ops_uu_scoped_real_ops_uu_constr_map_ops_uu_uu_Pair_show_state_vec_ops_uu_api_input_dims_uu_uu_Pair_uu_uu_show_state_vec_ops_uu_api_input_dims_uu(api_input,
                                c, b, t_code, a_code, pos)

def scoped_fn_real_op_scale[A, B, C,
                             D](x0: scoped_fn_basic_ops_ext[A, B, real, C,
                     scoped_fn_real_ops_ext[A, D]]):
      A => real => A
  =
  x0 match {
  case scoped_fn_basic_ops_exta(scoped_fn_op_alpha, scoped_fn_op_scope_alpha,
                                 scoped_fn_op_scope, scoped_fn_op_from_fn,
                                 scoped_fn_op_invar, scoped_fn_op_inst,
                                 scoped_fn_op_eval,
                                 scoped_fn_real_ops_exta(scoped_fn_real_op_scale,
                  scoped_fn_real_op_diff, more))
    => scoped_fn_real_op_scale
}

def scoped_fn_real_op_diff[A, B, C,
                            D](x0: scoped_fn_basic_ops_ext[A, B, real, C,
                    scoped_fn_real_ops_ext[A, D]]):
      A => A => A
  =
  x0 match {
  case scoped_fn_basic_ops_exta(scoped_fn_op_alpha, scoped_fn_op_scope_alpha,
                                 scoped_fn_op_scope, scoped_fn_op_from_fn,
                                 scoped_fn_op_invar, scoped_fn_op_inst,
                                 scoped_fn_op_eval,
                                 scoped_fn_real_ops_exta(scoped_fn_real_op_scale,
                  scoped_fn_real_op_diff, more))
    => scoped_fn_real_op_diff
}

def scoped_tree_eval_vec_ops_uu[A](api_input:
                                     api_input_ext[nat,
            (DiffArray.T[Option[real]], nat), Unit],
                                    x1: Scoped_Tree[A], v: (Array.T[nat], nat)):
      A
  =
  (api_input, x1, v) match {
  case (api_input, Scoped_Leaf(y), v) => y
  case (api_input, Scoped_Node(i, arr), v) =>
    {
      val j =
        (vec_op_idx[(Array.T[nat], nat), nat, nat,
                     Unit](vec_ops_uua(api_input))).apply(v).apply(i):
          nat
      val true = less_nat(j, length[Scoped_Tree[A]](arr)): Boolean;
      scoped_tree_eval_vec_ops_uu[A](api_input, sub[Scoped_Tree[A]](arr, j), v)
    }
}

def SR_scoped_tree_to_scoped_fn_scoped_real_ops_uu_vec_ops_uu(api_input:
                        api_input_ext[nat, (DiffArray.T[Option[real]], nat),
                                       Unit],
                       f: Scoped_Tree[real], s: nat):
      (((Array.T[nat], nat)) => real, nat)
  =
  (scoped_fn_op_from_fn[(((Array.T[nat], nat)) => real, nat),
                         (Array.T[nat], nat), real, nat,
                         scoped_fn_real_ops_ext[(((Array.T[nat], nat)) => real,
          nat),
         Unit]](scoped_real_ops_uua(api_input))).apply(s).apply(((a:
                            (Array.T[nat], nat))
                           =>
                          scoped_tree_eval_vec_ops_uu[real](api_input, f, a)))

def api_input_h_scope_code[A, B, C](x0: api_input_ext[A, B, C]): nat => A = x0
  match {
  case api_input_exta(api_input_dims, api_input_doms, api_input_t_max_code,
                       api_input_epsilon_code, api_input_rewards_code_fn,
                       api_input_rewards_scope_code, api_input_reward_dim_code,
                       api_input_actions_code, api_input_d_code,
                       api_input_transitions_code_fn,
                       api_input_transitions_scopes_code, api_input_l_code,
                       api_input_h_code_fn, api_input_h_scope_code,
                       api_input_h_dim_code, api_input_effects_code, more)
    => api_input_h_scope_code
}

def api_input_h_dim_code[A, B, C](x0: api_input_ext[A, B, C]): nat = x0 match {
  case api_input_exta(api_input_dims, api_input_doms, api_input_t_max_code,
                       api_input_epsilon_code, api_input_rewards_code_fn,
                       api_input_rewards_scope_code, api_input_reward_dim_code,
                       api_input_actions_code, api_input_d_code,
                       api_input_transitions_code_fn,
                       api_input_transitions_scopes_code, api_input_l_code,
                       api_input_h_code_fn, api_input_h_scope_code,
                       api_input_h_dim_code, api_input_effects_code, more)
    => api_input_h_dim_code
}

def api_input_h_code_fn[A, B, C](x0: api_input_ext[A, B, C]):
      nat => Scoped_Tree[real]
  =
  x0 match {
  case api_input_exta(api_input_dims, api_input_doms, api_input_t_max_code,
                       api_input_epsilon_code, api_input_rewards_code_fn,
                       api_input_rewards_scope_code, api_input_reward_dim_code,
                       api_input_actions_code, api_input_d_code,
                       api_input_transitions_code_fn,
                       api_input_transitions_scopes_code, api_input_l_code,
                       api_input_h_code_fn, api_input_h_scope_code,
                       api_input_h_dim_code, api_input_effects_code, more)
    => api_input_h_code_fn
}

def h_code_scoped_real_ops_uu_vec_ops_uu_uu(api_input:
      api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit]):
      nat => (((Array.T[nat], nat)) => real, nat)
  =
  {
    val a =
      of_fun[(((Array.T[nat], nat)) => real,
               nat)](((i: nat) =>
                       SR_scoped_tree_to_scoped_fn_scoped_real_ops_uu_vec_ops_uu(api_input,
  (api_input_h_code_fn[nat, (DiffArray.T[Option[real]], nat),
                        Unit](api_input)).apply(i),
  (api_input_h_scope_code[nat, (DiffArray.T[Option[real]], nat),
                           Unit](api_input)).apply(i))),
                      api_input_h_dim_code[nat,
    (DiffArray.T[Option[real]], nat), Unit](api_input)):
        (Array.T[((((Array.T[nat], nat)) => real, nat))]);
    ((b: nat) => sub[(((Array.T[nat], nat)) => real, nat)](a, b))
  }

def api_input_l_code[A, B, C](x0: api_input_ext[A, B, C]): real = x0 match {
  case api_input_exta(api_input_dims, api_input_doms, api_input_t_max_code,
                       api_input_epsilon_code, api_input_rewards_code_fn,
                       api_input_rewards_scope_code, api_input_reward_dim_code,
                       api_input_actions_code, api_input_d_code,
                       api_input_transitions_code_fn,
                       api_input_transitions_scopes_code, api_input_l_code,
                       api_input_h_code_fn, api_input_h_scope_code,
                       api_input_h_dim_code, api_input_effects_code, more)
    => api_input_l_code
}

def bellman_diff_code_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_scoped_real_ops_uu_uu_uu(api_input:
                             api_input_ext[nat,
    (DiffArray.T[Option[real]], nat), Unit],
                            g_cache:
                              nat =>
                                nat => (((Array.T[nat], nat)) => real, nat),
                            a_code: nat, i: nat):
      (((Array.T[nat], nat)) => real, nat)
  =
  (scoped_fn_real_op_diff[(((Array.T[nat], nat)) => real, nat),
                           (Array.T[nat], nat), nat,
                           Unit](scoped_real_ops_uua(api_input))).apply((h_code_scoped_real_ops_uu_vec_ops_uu_uu(api_input)).apply(i)).apply((scoped_fn_real_op_scale[(((Array.T[nat],
         nat)) =>
         real,
        nat),
       (Array.T[nat], nat), nat,
       Unit](scoped_real_ops_uua(api_input))).apply((g_cache(i))(a_code)).apply(api_input_l_code[nat,
                  (DiffArray.T[Option[real]], nat), Unit](api_input)))

def hg_inst_code_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_scoped_real_ops_uu_uu_uu_uu(api_input:
                           api_input_ext[nat, (DiffArray.T[Option[real]], nat),
  Unit],
                          g_cache:
                            nat => nat => (((Array.T[nat], nat)) => real, nat),
                          t_code: (Array.T[nat], nat), a_code: nat, i: nat):
      (((Array.T[nat], nat)) => real, nat)
  =
  (scoped_fn_op_inst[(((Array.T[nat], nat)) => real, nat), (Array.T[nat], nat),
                      real, nat,
                      scoped_fn_real_ops_ext[(((Array.T[nat], nat)) => real,
       nat),
      Unit]](scoped_real_ops_uua(api_input))).apply(bellman_diff_code_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_scoped_real_ops_uu_uu_uu(api_input,
                                    g_cache, a_code, i)).apply(t_code)

def C_code_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_real_ops_uu_uu_uu_uu(api_input:
     api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
    g_cache: nat => nat => (((Array.T[nat], nat)) => real, nat),
    t_code: (Array.T[nat], nat), a_code: nat):
      List[(((Array.T[nat], nat)) => real, nat)]
  =
  map[nat, (((Array.T[nat], nat)) => real,
             nat)](((a: nat) =>
                     hg_inst_code_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_scoped_real_ops_uu_uu_uu_uu(api_input,
   g_cache, t_code, a_code, a)),
                    upt.apply(zero_nata).apply(api_input_h_dim_code[nat,
                             (DiffArray.T[Option[real]], nat),
                             Unit](api_input)))

def C_code_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_real_ops_uu_uu_uu_uua(api_input:
      api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
     g_cache: nat => nat => (((Array.T[nat], nat)) => real, nat),
     t_code: (Array.T[nat], nat), a_code: nat):
      List[(((Array.T[nat], nat)) => real, nat)]
  =
  C_code_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_real_ops_uu_uu_uu_uu(api_input,
  g_cache, t_code, a_code)

def api_input_rewards_scope_code[A, B, C](x0: api_input_ext[A, B, C]):
      nat => nat => A
  =
  x0 match {
  case api_input_exta(api_input_dims, api_input_doms, api_input_t_max_code,
                       api_input_epsilon_code, api_input_rewards_code_fn,
                       api_input_rewards_scope_code, api_input_reward_dim_code,
                       api_input_actions_code, api_input_d_code,
                       api_input_transitions_code_fn,
                       api_input_transitions_scopes_code, api_input_l_code,
                       api_input_h_code_fn, api_input_h_scope_code,
                       api_input_h_dim_code, api_input_effects_code, more)
    => api_input_rewards_scope_code
}

def api_input_rewards_code_fn[A, B, C](x0: api_input_ext[A, B, C]):
      nat => nat => Scoped_Tree[real]
  =
  x0 match {
  case api_input_exta(api_input_dims, api_input_doms, api_input_t_max_code,
                       api_input_epsilon_code, api_input_rewards_code_fn,
                       api_input_rewards_scope_code, api_input_reward_dim_code,
                       api_input_actions_code, api_input_d_code,
                       api_input_transitions_code_fn,
                       api_input_transitions_scopes_code, api_input_l_code,
                       api_input_h_code_fn, api_input_h_scope_code,
                       api_input_h_dim_code, api_input_effects_code, more)
    => api_input_rewards_code_fn
}

def api_input_reward_dim_code[A, B, C](x0: api_input_ext[A, B, C]): nat => nat =
  x0 match {
  case api_input_exta(api_input_dims, api_input_doms, api_input_t_max_code,
                       api_input_epsilon_code, api_input_rewards_code_fn,
                       api_input_rewards_scope_code, api_input_reward_dim_code,
                       api_input_actions_code, api_input_d_code,
                       api_input_transitions_code_fn,
                       api_input_transitions_scopes_code, api_input_l_code,
                       api_input_h_code_fn, api_input_h_scope_code,
                       api_input_h_dim_code, api_input_effects_code, more)
    => api_input_reward_dim_code
}

def api_input_actions_code[A, B, C](x0: api_input_ext[A, B, C]): nat = x0 match
  {
  case api_input_exta(api_input_dims, api_input_doms, api_input_t_max_code,
                       api_input_epsilon_code, api_input_rewards_code_fn,
                       api_input_rewards_scope_code, api_input_reward_dim_code,
                       api_input_actions_code, api_input_d_code,
                       api_input_transitions_code_fn,
                       api_input_transitions_scopes_code, api_input_l_code,
                       api_input_h_code_fn, api_input_h_scope_code,
                       api_input_h_dim_code, api_input_effects_code, more)
    => api_input_actions_code
}

def api_input_d_code[A, B, C](x0: api_input_ext[A, B, C]): nat = x0 match {
  case api_input_exta(api_input_dims, api_input_doms, api_input_t_max_code,
                       api_input_epsilon_code, api_input_rewards_code_fn,
                       api_input_rewards_scope_code, api_input_reward_dim_code,
                       api_input_actions_code, api_input_d_code,
                       api_input_transitions_code_fn,
                       api_input_transitions_scopes_code, api_input_l_code,
                       api_input_h_code_fn, api_input_h_scope_code,
                       api_input_h_dim_code, api_input_effects_code, more)
    => api_input_d_code
}

def rewards_code_scoped_real_ops_uu_vec_ops_uu_uu(api_input:
            api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit]):
      nat => nat => (((Array.T[nat], nat)) => real, nat)
  =
  {
    val drs =
      of_fun[(((Array.T[nat], nat)) => real,
               nat)](((i: nat) =>
                       SR_scoped_tree_to_scoped_fn_scoped_real_ops_uu_vec_ops_uu(api_input,
  (api_input_rewards_code_fn[nat, (DiffArray.T[Option[real]], nat),
                              Unit](api_input)).apply(api_input_d_code[nat,
                                (DiffArray.T[Option[real]], nat),
                                Unit](api_input)).apply(i),
  (api_input_rewards_scope_code[nat, (DiffArray.T[Option[real]], nat),
                                 Unit](api_input)).apply(api_input_d_code[nat,
                                   (DiffArray.T[Option[real]], nat),
                                   Unit](api_input)).apply(minus_nata(i,
                               (if (equal_nata(api_input_d_code[nat,
                         (DiffArray.T[Option[real]], nat), Unit](api_input),
        api_input_d_code[nat, (DiffArray.T[Option[real]], nat),
                          Unit](api_input)))
                                 zero_nata
                                 else (api_input_reward_dim_code[nat,
                          (DiffArray.T[Option[real]], nat),
                          Unit](api_input)).apply(api_input_d_code[nat,
                            (DiffArray.T[Option[real]], nat),
                            Unit](api_input))))))),
                      plus_nata((api_input_reward_dim_code[nat,
                    (DiffArray.T[Option[real]], nat),
                    Unit](api_input)).apply(api_input_d_code[nat,
                      (DiffArray.T[Option[real]], nat), Unit](api_input)),
                                 (if (equal_nata(api_input_d_code[nat,
                           (DiffArray.T[Option[real]], nat), Unit](api_input),
          api_input_d_code[nat, (DiffArray.T[Option[real]], nat),
                            Unit](api_input)))
                                   zero_nata
                                   else (api_input_reward_dim_code[nat,
                            (DiffArray.T[Option[real]], nat),
                            Unit](api_input)).apply(api_input_d_code[nat,
                              (DiffArray.T[Option[real]], nat),
                              Unit](api_input))))):
        (Array.T[((((Array.T[nat], nat)) => real, nat))])
    val rs =
      of_fun[Array.T[((((Array.T[nat], nat)) => real,
                       nat))]](((a: nat) =>
                                 of_fun[(((Array.T[nat], nat)) => real,
  nat)](((i: nat) =>
          (if (less_nat(i, plus_nata((api_input_reward_dim_code[nat,
                         (DiffArray.T[Option[real]], nat),
                         Unit](api_input)).apply(api_input_d_code[nat,
                           (DiffArray.T[Option[real]], nat), Unit](api_input)),
                                      (if (equal_nata(api_input_d_code[nat,
                                (DiffArray.T[Option[real]], nat),
                                Unit](api_input),
               api_input_d_code[nat, (DiffArray.T[Option[real]], nat),
                                 Unit](api_input)))
zero_nata
else (api_input_reward_dim_code[nat, (DiffArray.T[Option[real]], nat),
                                 Unit](api_input)).apply(api_input_d_code[nat,
                                   (DiffArray.T[Option[real]], nat),
                                   Unit](api_input))))))
            sub[(((Array.T[nat], nat)) => real, nat)](drs, i)
            else {
                   val ia =
                     minus_nata(i, plus_nata((api_input_reward_dim_code[nat,
                                 (DiffArray.T[Option[real]], nat),
                                 Unit](api_input)).apply(api_input_d_code[nat,
                                   (DiffArray.T[Option[real]], nat),
                                   Unit](api_input)),
      (if (equal_nata(api_input_d_code[nat, (DiffArray.T[Option[real]], nat),
Unit](api_input),
                       api_input_d_code[nat, (DiffArray.T[Option[real]], nat),
 Unit](api_input)))
        zero_nata
        else (api_input_reward_dim_code[nat, (DiffArray.T[Option[real]], nat),
 Unit](api_input)).apply(api_input_d_code[nat, (DiffArray.T[Option[real]], nat),
   Unit](api_input))))):
                       nat;
                   SR_scoped_tree_to_scoped_fn_scoped_real_ops_uu_vec_ops_uu(api_input,
                                      (api_input_rewards_code_fn[nat,
                          (DiffArray.T[Option[real]], nat),
                          Unit](api_input)).apply(a).apply(ia),
                                      (api_input_rewards_scope_code[nat,
                             (DiffArray.T[Option[real]], nat),
                             Unit](api_input)).apply(a).apply(ia))
                 })),
         plus_nata((api_input_reward_dim_code[nat,
       (DiffArray.T[Option[real]], nat), Unit](api_input)).apply(a),
                    (if (equal_nata(a, api_input_d_code[nat,
                 (DiffArray.T[Option[real]], nat), Unit](api_input)))
                      zero_nata
                      else (api_input_reward_dim_code[nat,
               (DiffArray.T[Option[real]], nat),
               Unit](api_input)).apply(api_input_d_code[nat,
                 (DiffArray.T[Option[real]], nat), Unit](api_input)))))),
                                api_input_actions_code[nat,
                (DiffArray.T[Option[real]], nat), Unit](api_input)):
        (Array.T[(Array.T[((((Array.T[nat], nat)) => real, nat))])]);
    ((a: nat) =>
      ((b: nat) =>
        sub[(((Array.T[nat], nat)) => real,
              nat)](sub[Array.T[((((Array.T[nat], nat)) => real, nat))]](rs, a),
                     b)))
  }

def r_inst_code_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_scoped_real_ops_uu_uu_uu(api_input:
         api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
        t_code: (Array.T[nat], nat), a_code: nat, i: nat):
      (((Array.T[nat], nat)) => real, nat)
  =
  (scoped_fn_op_inst[(((Array.T[nat], nat)) => real, nat), (Array.T[nat], nat),
                      real, nat,
                      scoped_fn_real_ops_ext[(((Array.T[nat], nat)) => real,
       nat),
      Unit]](scoped_real_ops_uua(api_input))).apply((rewards_code_scoped_real_ops_uu_vec_ops_uu_uu(api_input)).apply(a_code).apply(i)).apply(t_code)

def b_code_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_scoped_real_ops_uu_uu_uu(api_input:
       api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
      t_code: (Array.T[nat], nat), a_code: nat):
      List[(((Array.T[nat], nat)) => real, nat)]
  =
  map[nat, (((Array.T[nat], nat)) => real,
             nat)](((a: nat) =>
                     r_inst_code_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_scoped_real_ops_uu_uu_uu(api_input,
                         t_code, a_code, a)),
                    upt.apply(zero_nata).apply(plus_nata((api_input_reward_dim_code[nat,
     (DiffArray.T[Option[real]], nat), Unit](api_input)).apply(a_code),
                  (if (equal_nata(a_code,
                                   api_input_d_code[nat,
             (DiffArray.T[Option[real]], nat), Unit](api_input)))
                    zero_nata
                    else (api_input_reward_dim_code[nat,
             (DiffArray.T[Option[real]], nat),
             Unit](api_input)).apply(api_input_d_code[nat,
               (DiffArray.T[Option[real]], nat), Unit](api_input))))))

def neg_b_code_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_scoped_real_ops_uu_uu_uu(api_input:
           api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
          t_code: (Array.T[nat], nat), a_code: nat):
      List[(((Array.T[nat], nat)) => real, nat)]
  =
  map[(((Array.T[nat], nat)) => real, nat),
       (((Array.T[nat], nat)) => real,
         nat)](((f: (((Array.T[nat], nat)) => real, nat)) =>
                 (scoped_fn_real_op_scale[(((Array.T[nat], nat)) => real, nat),
   (Array.T[nat], nat), nat,
   Unit](scoped_real_ops_uua(api_input))).apply(f).apply(uminus_reala(one_reala))),
                b_code_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_scoped_real_ops_uu_uu_uu(api_input,
                  t_code, a_code))

def scoped_fn_ereal_op_ind[A, B, C,
                            D](x0: scoped_fn_basic_ops_ext[A, B, ereal, C,
                    scoped_fn_ereal_ops_ext[A, B, D]]):
      B => A
  =
  x0 match {
  case scoped_fn_basic_ops_exta(scoped_fn_op_alpha, scoped_fn_op_scope_alpha,
                                 scoped_fn_op_scope, scoped_fn_op_from_fn,
                                 scoped_fn_op_invar, scoped_fn_op_inst,
                                 scoped_fn_op_eval,
                                 scoped_fn_ereal_ops_exta(scoped_fn_ereal_op_ind,
                   more))
    => scoped_fn_ereal_op_ind
}

def I_code_scoped_ereal_ops_uu_uu_uu(api_input:
                                       api_input_ext[nat,
              (DiffArray.T[Option[real]], nat), Unit],
                                      ts_code: List[(Array.T[nat], nat)],
                                      t_code: (Array.T[nat], nat)):
      List[(((Array.T[nat], nat)) => ereal, nat)]
  =
  map[(Array.T[nat], nat),
       (((Array.T[nat], nat)) => ereal,
         nat)](((t: (Array.T[nat], nat)) =>
                 (scoped_fn_op_inst[(((Array.T[nat], nat)) => ereal, nat),
                                     (Array.T[nat], nat), ereal, nat,
                                     scoped_fn_ereal_ops_ext[(((Array.T[nat],
                        nat)) =>
                        ereal,
                       nat),
                      (Array.T[nat], nat),
                      Unit]](scoped_ereal_ops_uua(api_input))).apply((scoped_fn_ereal_op_ind[(((Array.T[nat],
                nat)) =>
                ereal,
               nat),
              (Array.T[nat], nat), nat,
              Unit](scoped_ereal_ops_uua(api_input))).apply(t)).apply(t_code)),
                ts_code)

def scoped_to_ereal[A, B](f: (A => real, B)): (A => ereal, B) =
  (comp[real, ereal, A](((a: real) => ereala(a)), fst[A => real, B](f)),
    scoped_scope[A, real, B](f))

def neg_b_code_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_scoped_real_ops_uu_ste_ops_scoped_ereal_ops_uu_uu_uu_uu(api_input:
  api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
 ts_code: List[(Array.T[nat], nat)], t_code: (Array.T[nat], nat), a_code: nat):
      List[(((Array.T[nat], nat)) => ereal, nat)]
  =
  map[(((Array.T[nat], nat)) => real, nat),
       (((Array.T[nat], nat)) => ereal,
         nat)](((a: (((Array.T[nat], nat)) => real, nat)) =>
                 scoped_to_ereal[(Array.T[nat], nat), nat](a)),
                neg_b_code_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_scoped_real_ops_uu_uu_uu(api_input,
                      t_code, a_code)) ++
    I_code_scoped_ereal_ops_uu_uu_uu(api_input, ts_code, t_code)

def Omega_pos_code_vec_ops_uu_set_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_real_ops_uu_ste_ops_scoped_ereal_ops_uu_constr_map_ops_uu_uu_uu_uu(api_input:
                     api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
                    g_cache: nat => nat => (((Array.T[nat], nat)) => real, nat),
                    ts_code: List[(Array.T[nat], nat)],
                    t_code: (Array.T[nat], nat), a_code: nat):
      List[Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
 List[Option[nat]]],
                                real]]]
  =
  factored_lp_code_vec_ops_uu_set_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_scoped_real_ops_uu_scoped_ereal_ops_uu_constr_map_ops_uu_uu(api_input,
                                 t_code, a_code, true,
                                 C_code_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_real_ops_uu_uu_uu_uua(api_input,
                                  g_cache, t_code, a_code),
                                 neg_b_code_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_scoped_real_ops_uu_ste_ops_scoped_ereal_ops_uu_uu_uu_uu(api_input,
                              ts_code, t_code, a_code))

def neg_C_code_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_real_ops_uu_uu_uu_uu(api_input:
         api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
        g_cache: nat => nat => (((Array.T[nat], nat)) => real, nat),
        t_code: (Array.T[nat], nat), a_code: nat):
      List[(((Array.T[nat], nat)) => real, nat)]
  =
  map[(((Array.T[nat], nat)) => real, nat),
       (((Array.T[nat], nat)) => real,
         nat)](((f: (((Array.T[nat], nat)) => real, nat)) =>
                 (scoped_fn_real_op_scale[(((Array.T[nat], nat)) => real, nat),
   (Array.T[nat], nat), nat,
   Unit](scoped_real_ops_uua(api_input))).apply(f).apply(uminus_reala(one_reala))),
                C_code_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_real_ops_uu_uu_uu_uu(api_input,
                g_cache, t_code, a_code))

def neg_C_code_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_real_ops_uu_uu_uu_uua(api_input:
          api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
         g_cache: nat => nat => (((Array.T[nat], nat)) => real, nat),
         t_code: (Array.T[nat], nat), a_code: nat):
      List[(((Array.T[nat], nat)) => real, nat)]
  =
  neg_C_code_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_real_ops_uu_uu_uu_uu(api_input,
      g_cache, t_code, a_code)

def b_code_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_scoped_real_ops_uu_ste_ops_scoped_ereal_ops_uu_uu_uu_uu(api_input:
                                      api_input_ext[nat,
             (DiffArray.T[Option[real]], nat), Unit],
                                     ts_code: List[(Array.T[nat], nat)],
                                     t_code: (Array.T[nat], nat), a_code: nat):
      List[(((Array.T[nat], nat)) => ereal, nat)]
  =
  map[(((Array.T[nat], nat)) => real, nat),
       (((Array.T[nat], nat)) => ereal,
         nat)](((a: (((Array.T[nat], nat)) => real, nat)) =>
                 scoped_to_ereal[(Array.T[nat], nat), nat](a)),
                b_code_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_scoped_real_ops_uu_uu_uu(api_input,
                  t_code, a_code)) ++
    I_code_scoped_ereal_ops_uu_uu_uu(api_input, ts_code, t_code)

def Omega_neg_code_vec_ops_uu_set_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_real_ops_uu_ste_ops_scoped_ereal_ops_uu_constr_map_ops_uu_uu_uu_uu(api_input:
                     api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
                    g_cache: nat => nat => (((Array.T[nat], nat)) => real, nat),
                    ts_code: List[(Array.T[nat], nat)],
                    t_code: (Array.T[nat], nat), a_code: nat):
      List[Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
 List[Option[nat]]],
                                real]]]
  =
  factored_lp_code_vec_ops_uu_set_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_scoped_real_ops_uu_scoped_ereal_ops_uu_constr_map_ops_uu_uu(api_input,
                                 t_code, a_code, false,
                                 neg_C_code_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_real_ops_uu_uu_uu_uua(api_input,
                                      g_cache, t_code, a_code),
                                 b_code_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_scoped_real_ops_uu_ste_ops_scoped_ereal_ops_uu_uu_uu_uu(api_input,
                          ts_code, t_code, a_code))

def Omega_code_vec_ops_uu_set_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_real_ops_uu_ste_ops_scoped_ereal_ops_uu_constr_map_ops_uu_uu_uu_uu(api_input:
                 api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
                g_cache: nat => nat => (((Array.T[nat], nat)) => real, nat),
                ts_code: List[(Array.T[nat], nat)], t_code: (Array.T[nat], nat),
                a_code: nat):
      List[Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
 List[Option[nat]]],
                                real]]]
  =
  Omega_pos_code_vec_ops_uu_set_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_real_ops_uu_ste_ops_scoped_ereal_ops_uu_constr_map_ops_uu_uu_uu_uu(api_input,
                  g_cache, ts_code, t_code, a_code) ++
    Omega_neg_code_vec_ops_uu_set_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_real_ops_uu_ste_ops_scoped_ereal_ops_uu_constr_map_ops_uu_uu_uu_uu(api_input,
                    g_cache, ts_code, t_code, a_code)

def gen_constr_code_vec_ops_uu_set_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_constr_map_ops_scoped_ereal_ops_uu_ste_ops_scoped_real_ops_uu_uu(api_input:
             api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
            g_cache: nat => nat => (((Array.T[nat], nat)) => real, nat),
            s: (Array.T[nat], nat), a: nat, ts: List[(Array.T[nat], nat)]):
      List[Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
 List[Option[nat]]],
                                real]]]
  =
  Omega_code_vec_ops_uu_set_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_real_ops_uu_ste_ops_scoped_ereal_ops_uu_constr_map_ops_uu_uu_uu_uu(api_input,
              g_cache, ts, s, a)

def update_weights_iter_code_vec_ops_uu_set_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_constr_map_ops_scoped_ereal_ops_uu_ste_ops_scoped_real_ops_uu_uu(api_input:
                      api_input_ext[nat, (DiffArray.T[Option[real]], nat),
                                     Unit],
                     g_cache:
                       nat => nat => (((Array.T[nat], nat)) => real, nat)):
      (((Array.T[nat], nat), nat)) =>
        ((List[(Array.T[nat], nat)],
          List[Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
     List[Option[nat]]],
                                    real]]])) =>
          (List[(Array.T[nat], nat)],
            List[Constr_Code[hashmap[var_code[(List[Option[nat]],
        (nat, Boolean)),
       List[Option[nat]]],
                                      real]]])
  =
  ((a: ((Array.T[nat], nat), nat)) =>
    {
      val (t, aa) = a: (((Array.T[nat], nat), nat));
      ((b: (List[(Array.T[nat], nat)],
             List[Constr_Code[hashmap[var_code[(List[Option[nat]],
         (nat, Boolean)),
        List[Option[nat]]],
                                       real]]]))
         =>
        {
          val (ts, cs) =
            b: ((List[(Array.T[nat], nat)],
                 List[Constr_Code[hashmap[var_code[(List[Option[nat]],
             (nat, Boolean)),
            List[Option[nat]]],
   real]]]));
          (t :: ts,
            gen_constr_code_vec_ops_uu_set_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_constr_map_ops_scoped_ereal_ops_uu_ste_ops_scoped_real_ops_uu_uu(api_input,
                    g_cache, t, aa, ts) ++
              cs)
        })
    })

def constrs_list_code_vec_ops_uu_set_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_constr_map_ops_scoped_ereal_ops_uu_ste_ops_scoped_real_ops_uu_uu(api_input:
               api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
              g_cache: nat => nat => (((Array.T[nat], nat)) => real, nat),
              xs: List[((Array.T[nat], nat), nat)]):
      List[Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
 List[Option[nat]]],
                                real]]]
  =
  snd[List[(Array.T[nat], nat)],
       List[Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
  List[Option[nat]]],
                                 real]]]](fold[((Array.T[nat], nat), nat),
        (List[(Array.T[nat], nat)],
          List[Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
     List[Option[nat]]],
                                    real]]])](update_weights_iter_code_vec_ops_uu_set_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_constr_map_ops_scoped_ereal_ops_uu_ste_ops_scoped_real_ops_uu_uu(api_input,
                       g_cache),
       xs, (Nil, Nil)))

def constrs_code_vec_ops_uu_set_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_constr_map_ops_scoped_ereal_ops_uu_ste_ops_scoped_real_ops_uu_uu_uu(api_input:
             api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
            dec_pol_code: List[((Array.T[nat], nat), nat)],
            g_cache: nat => nat => (((Array.T[nat], nat)) => real, nat)):
      List[Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
 List[Option[nat]]],
                                real]]]
  =
  constrs_list_code_vec_ops_uu_set_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_constr_map_ops_scoped_ereal_ops_uu_ste_ops_scoped_real_ops_uu_uu(api_input,
            g_cache, dec_pol_code)

def obj_code_constr_map_ops:
      hashmap[var_code[(List[Option[nat]], (nat, Boolean)), List[Option[nat]]],
               real]
  =
  g_list_to_map_ahm_basic_ops[var_code[(List[Option[nat]], (nat, Boolean)),
List[Option[nat]]],
                               real](List((var_phi[(List[Option[nat]],
             (nat, Boolean)),
            List[Option[nat]]](),
    one_reala)))

def lp_code_vec_ops_uu_set_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_constr_map_ops_scoped_ereal_ops_uu_ste_ops_scoped_real_ops_uu_uu_uu(api_input:
        api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
       dec_pol_code: List[((Array.T[nat], nat), nat)],
       g_cache: nat => nat => (((Array.T[nat], nat)) => real, nat)):
      LP_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                                List[Option[nat]]],
                       real]]
  =
  LP_Codea[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                             List[Option[nat]]],
                    real]](obj_code_constr_map_ops,
                            constrs_code_vec_ops_uu_set_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_constr_map_ops_scoped_ereal_ops_uu_ste_ops_scoped_real_ops_uu_uu_uu(api_input,
                                    dec_pol_code, g_cache))

def neg_constraint_expr: (List[(nat, real)]) => List[(nat, real)] =
  ((a: List[(nat, real)]) =>
    map[(nat, real),
         (nat, real)](((aa: (nat, real)) => {
      val (i, x) = aa: ((nat, real));
      (i, uminus_reala(x))
    }),
                       a))

def constraint_to_le[A : uminus](x0: (List[(nat, real)], (sense, A))):
      List[(List[(nat, real)], A)]
  =
  x0 match {
  case (p, (Leq(), b)) => List((p, b))
  case (p, (Geq(), b)) => List((neg_constraint_expr.apply(p), uminus[A](b)))
  case (p, (Eqa(), b)) =>
    List((neg_constraint_expr.apply(p), uminus[A](b)), (p, b))
}

def constraints_to_le[A : uminus](cs: List[(List[(nat, real)], (sense, A))]):
      List[(List[(nat, real)], A)]
  =
  maps[(List[(nat, real)], (sense, A)),
        (List[(nat, real)],
          A)](((a: (List[(nat, real)], (sense, A))) => constraint_to_le[A](a)),
               cs)

def upd_list[A : equal : linorder, B](x: A, y: B, xa2: List[(A, B)]):
      List[(A, B)]
  =
  (x, y, xa2) match {
  case (x, y, Nil) => List((x, y))
  case (x, y, (a, b) :: ps) =>
    (if (less[A](x, a)) (x, y) :: (a, b) :: ps
      else (if (eq[A](x, a)) (x, y) :: ps
             else (a, b) :: upd_list[A, B](x, y, ps)))
}

def am_update[A : equal : linorder, B]: A => B => (List[(A, B)]) => List[(A, B)]
  =
  ((a: A) => (b: B) => (c: List[(A, B)]) => upd_list[A, B](a, b, c))

def am_empty[A]: List[A] = Nil

def from_list2_am_empty_am_update[A : equal : linorder, B](xs: List[(A, B)]):
      List[(A, B)]
  =
  foldl[List[(A, B)],
         (A, B)](((acc: List[(A, B)]) => (a: (A, B)) =>
                   {
                     val (k, v) = a: ((A, B));
                     am_update[A, B].apply(k).apply(v).apply(acc)
                   }),
                  am_empty[(A, B)], xs)

def constraints_to_map_am_empty_am_update[A : uminus](cs:
                List[(List[(nat, real)], (sense, A))]):
      (List[List[(nat, real)]], List[A])
  =
  {
    val (a, b) =
      unzip[List[(nat, real)], A](constraints_to_le[A](cs)):
        ((List[List[(nat, real)]], List[A]));
    (map[List[(nat, real)],
          List[(nat, real)]](((aa: List[(nat, real)]) =>
                               from_list2_am_empty_am_update[nat, real](aa)),
                              a),
      b)
  }

def from_file_am_empty_am_update_am_empty_am_update[A](m: Boolean, n: A,
                c: List[(nat, real)],
                cs: List[(List[(nat, real)], (sense, real))]):
      (A, (List[(nat, real)],
            (List[(nat, List[(nat, real)])], List[(nat, real)])))
  =
  (n, (from_list2_am_empty_am_update[nat, real]((if (m) c
          else neg_constraint_expr.apply(c))),
        {
          val (c2, b2) =
            constraints_to_map_am_empty_am_update[real](cs):
              ((List[List[(nat, real)]], List[real]));
          (enumerate[List[(nat, real)]](zero_nata, c2),
            enumerate[real](zero_nata, b2))
        }))

def sorted1_code[A : linorder, B]: (List[(A, B)]) => Boolean =
  ((a: List[(A, B)]) =>
    (a match {
       case Nil => true
       case List(_) => true
       case x :: y :: ys =>
         less[A](fst[A, B](x), fst[A, B](y)) &&
           sorted1_code[A, B].apply(y :: ys)
     }))

def am_invar[A : linorder, B]: (List[(A, B)]) => Boolean = sorted1_code[A, B]

def invar_id_am_invar[A : linorder, B](t: List[(A, B)]): Boolean =
  am_invar[A, B].apply(t) && sorted1_code[A, B].apply(t)

def rat_pair_le(x: rat_pair, xb: rat_pair): Boolean =
  ({
     val (a, b) = Rep_rat_pair(x): ((int, int));
     ((c: (int, int)) =>
       {
         val (ca, d) = c: ((int, int))
         val da = times_int(b, d): int;
         less_eq_int(times_int(times_int(a, d), da),
                      times_int(times_int(ca, b), da))
       })
   })(Rep_rat_pair(xb))

def less_eq_real_code(x0: real_code, x1: real_code): Boolean = (x0, x1) match {
  case (Frcta(x), Frcta(y)) => rat_pair_le(x, y)
}

def zero_rat_pair: rat_pair = Abs_rat_pair((zero_int, one_int))

def zero_real_code: real_code = Frcta(zero_rat_pair)

def combine_lists[A, B,
                   C](f: A => B => C => C, uv: List[(nat, A)],
                       uw: List[(nat, B)], acc: C):
      C
  =
  (f, uv, uw, acc) match {
  case (f, (i, x) :: xs, (j, y) :: ys, acc) =>
    (if (less_nat(i, j)) combine_lists[A, B, C](f, xs, (j, y) :: ys, acc)
      else (if (less_nat(j, i)) combine_lists[A, B, C](f, (i, x) :: xs, ys, acc)
             else combine_lists[A, B, C](f, xs, ys, ((f(x))(y))(acc))))
  case (uu, Nil, uw, acc) => acc
  case (uu, uv, Nil, acc) => acc
}

def scalar_prod_code_id(x: List[(nat, real)], y: List[(nat, real)]): real_code =
  combine_lists[real, real,
                 real_code](((a: real) => (b: real) => (c: real_code) =>
                              mult_add(a, b, c)),
                             x, y, zero_real_code)

def A_times_x_id_id(a: List[(nat, List[(nat, real)])], x: List[(nat, real)]):
      List[(nat, real_code)]
  =
  map[(nat, List[(nat, real)]),
       (nat, real_code)](((aa: (nat, List[(nat, real)])) =>
                           {
                             val (j, v) = aa: ((nat, List[(nat, real)]));
                             (j, scalar_prod_code_id(v, x))
                           }),
                          a)

def combine_listsa[A, B,
                    C](f: nat => A => B => C => C, dx: A, dy: B,
                        x3: List[(nat, A)], x4: List[(nat, B)], acc: C):
      C
  =
  (f, dx, dy, x3, x4, acc) match {
  case (f, dx, dy, (i, x) :: xs, (j, y) :: ys, acc) =>
    (if (less_nat(i, j))
      combine_listsa[A, B,
                      C](f, dx, dy, xs, (j, y) :: ys, (((f(i))(x))(dy))(acc))
      else (if (less_nat(j, i))
             combine_listsa[A, B,
                             C](f, dx, dy, (i, x) :: xs, ys,
                                 (((f(j))(dx))(y))(acc))
             else combine_listsa[A, B,
                                  C](f, dx, dy, xs, ys, (((f(i))(x))(y))(acc))))
  case (f, dx, dy, (i, x) :: xs, Nil, acc) =>
    combine_listsa[A, B, C](f, dx, dy, xs, Nil, (((f(i))(x))(dy))(acc))
  case (f, dx, dy, Nil, (j, y) :: ys, acc) =>
    combine_listsa[A, B, C](f, dx, dy, Nil, ys, (((f(j))(dx))(y))(acc))
  case (f, dx, dy, Nil, Nil, acc) => acc
}

def check_feas_primal_id_id(a: List[(nat, List[(nat, real)])],
                             b: List[(nat, real)], x: List[(nat, real)]):
      Boolean
  =
  combine_listsa[real_code, real,
                  Boolean](((_: nat) => (l: real_code) => (r: real) =>
                             (acc: Boolean) =>
                             acc && less_eq_real_code(l, real_to_code(r))),
                            zero_real_code, zero_reala, A_times_x_id_id(a, x),
                            b, true)

def rat_pair_eq(x: rat_pair, xb: rat_pair): Boolean =
  ({
     val (n1, d1) = Rep_rat_pair(x): ((int, int));
     ((a: (int, int)) => {
                           val (n2, d2) = a: ((int, int));
                           equal_inta(times_int(n1, d2), times_int(n2, d1))
                         })
   })(Rep_rat_pair(xb))

def equal_real_code(x0: real_code, x1: real_code): Boolean = (x0, x1) match {
  case (Frcta(x), Frcta(y)) => rat_pair_eq(x, y)
}

def merge_lists[A](f: A => A => A, x1: List[(nat, A)], x2: List[(nat, A)],
                    acc: List[(nat, A)]):
      List[(nat, A)]
  =
  (f, x1, x2, acc) match {
  case (f, (i, x) :: xs, (j, y) :: ys, acc) =>
    (if (less_nat(i, j)) merge_lists[A](f, xs, (j, y) :: ys, (i, x) :: acc)
      else (if (less_nat(j, i))
             merge_lists[A](f, (i, x) :: xs, ys, (j, y) :: acc)
             else merge_lists[A](f, xs, ys, (i, (f(x))(y)) :: acc)))
  case (f, (i, x) :: xs, Nil, acc) => merge_lists[A](f, xs, Nil, (i, x) :: acc)
  case (f, Nil, (j, y) :: ys, acc) => merge_lists[A](f, Nil, ys, (j, y) :: acc)
  case (f, Nil, Nil, acc) => rev[(nat, A)](acc)
}

def y_times_A_id_id(a: List[(nat, List[(nat, real)])], y: List[(nat, real)]):
      List[(nat, real_code)]
  =
  combine_lists[real, List[(nat, real)],
                 List[(nat, real_code)]](((ya: real) =>
   (ar: List[(nat, real)]) => (acc: List[(nat, real_code)]) =>
   merge_lists[real_code](((aa: real_code) => (b: real_code) =>
                            add_real_code(aa, b)),
                           map[(nat, real),
                                (nat, real_code)](((aa: (nat, real)) =>
            {
              val (j, ab) = aa: ((nat, real));
              (j, mul_real_code(real_to_code(ya), real_to_code(ab)))
            }),
           ar),
                           acc, Nil)),
  y, a, Nil)

def check_feas_dual_id_id(a: List[(nat, List[(nat, real)])],
                           c: List[(nat, real)], y: List[(nat, real)]):
      Boolean
  =
  combine_listsa[real_code, real,
                  Boolean](((_: nat) => (l: real_code) => (r: real) =>
                             (acc: Boolean) =>
                             acc && equal_real_code(l, real_to_code(r))),
                            zero_real_code, zero_reala, y_times_A_id_id(a, y),
                            c, true) &&
    list_all[(nat, real)](((aa: (nat, real)) =>
                            {
                              val (_, r) = aa: ((nat, real));
                              less_eq_real(r, zero_reala)
                            }),
                           y)

def check_feas_id_id(a: List[(nat, List[(nat, real)])], b: List[(nat, real)],
                      c: List[(nat, real)], x: List[(nat, real)],
                      y: List[(nat, real)]):
      Boolean
  =
  check_feas_primal_id_id(a, b, x) && check_feas_dual_id_id(a, c, y)

def check_duality_id(b: List[(nat, real)], c: List[(nat, real)],
                      x: List[(nat, real)], y: List[(nat, real)]):
      Boolean
  =
  equal_real_code(scalar_prod_code_id(c, x), scalar_prod_code_id(b, y))

def check_opt_id_id(a: List[(nat, List[(nat, real)])], b: List[(nat, real)],
                     c: List[(nat, real)], x_code: List[(nat, real)],
                     y_code: List[(nat, real)]):
      Boolean
  =
  check_feas_id_id(a, b, c, x_code, y_code) &&
    check_duality_id(b, c, x_code, y_code)

def check_opt_id_am_invar_id(a: List[(nat, List[(nat, real)])],
                              b: List[(nat, real)], c: List[(nat, real)],
                              x_code: List[(nat, real)],
                              y_code: List[(nat, real)]):
      Boolean
  =
  invar_id_am_invar[nat, real](x_code) &&
    invar_id_am_invar[nat, real](y_code) &&
    check_opt_id_id(a, b, c, x_code, y_code)

def check_cert_id_am_invar_id(cert: LP_Cert[List[(nat, real)]],
                               a: List[(nat, List[(nat, real)])],
                               b: List[(nat, real)], c: List[(nat, real)]):
      Boolean
  =
  (cert match {
     case Cert_Opt(d, e) => check_opt_id_am_invar_id(a, b, c, d, e)
     case Cert_Infeas(_) => false
     case Cert_Unbounded(_, _) => false
   })

def solve_lp_am_empty_am_update_id_am_invar_am_empty_id_am_update_uu[A](lp_oracle:
                                  nat =>
                                    (List[(nat, real)]) =>
                                      (List[(nat, List[(nat, real)])]) =>
(List[(nat, real)]) => Option[LP_Cert[List[(nat, real)]]],
                                 lp_vm:
                                   ((Boolean,
                                      (nat,
(List[(nat, real)], List[(List[(nat, real)], (sense, real))]))),
                                     A)):
      Option[List[(nat, real)]]
  =
  {
    val ((m, (n, (c, cs))), _) =
      lp_vm:
        (((Boolean,
            (nat, (List[(nat, real)],
                    List[(List[(nat, real)], (sense, real))]))),
          A))
    val (na, (ca, (csa, bs))) =
      from_file_am_empty_am_update_am_empty_am_update[nat](m, n, c, cs):
        ((nat,
          (List[(nat, real)],
            (List[(nat, List[(nat, real)])], List[(nat, real)]))));
    ((((lp_oracle(na))(ca))(csa))(bs) match {
       case None => None
       case Some(Cert_Opt(x, y)) =>
         (if (check_cert_id_am_invar_id(Cert_Opt[List[(nat, real)]](x, y), csa,
 bs, ca))
           Some[List[(nat, real)]](x) else None)
       case Some(Cert_Infeas(_)) => None
       case Some(Cert_Unbounded(_, _)) => None
     })
  }

def ahm_alpha_aux[A : equal : hashable,
                   B](a: DiffArray.T[(List[(A, B)])], k: A):
      Option[B]
  =
  map_of[A, B]((array_get[List[(A, B)]](a)).apply(bounded_hashcode_nat[A](array_length[List[(A,
              B)]].apply(a),
                                   k)),
                k)

def ahm_alpha[A : equal : hashable, B](x0: hashmapa[A, B]): A => Option[B] = x0
  match {
  case HashMapa(a, uu) => ((b: A) => ahm_alpha_aux[A, B](a, b))
}

def ahm_lookupa[A : equal : hashable, B](k: A, hm: hashmapa[A, B]): Option[B] =
  (ahm_alpha[A, B](hm)).apply(k)

def ahm_lookup[A : equal : hashable, B](k: A, hm: hashmap[A, B]): Option[B] =
  ahm_lookupa[A, B](k, impl_of[A, B](hm))

def lookup0_code_constr_map_ops[A : equal : hashable](k: A,
               m: hashmap[A, real]):
      real
  =
  (ahm_lookup[A, real](k, m) match {
     case None => zero_reala
     case Some(y) => y
   })

def nat_to_var[A, B, C](m: (A, (B, List[C]))): nat => C =
  {
    val (_, (_, ma)) = m: ((A, (B, List[C])))
    val a = Array.init_list[C](rev[C](ma)): (Array.T[C]);
    ((b: nat) => sub[C](a, b))
  }

def num_vars[A, B, C](m: (A, (B, C))): B = {
     val (_, (n, _)) = m: ((A, (B, C)));
     n
   }

def lp_minimize_num_vars_am_empty_am_update_id_am_invar_am_empty_id_constr_map_ops_am_update_nat_to_var_uu(lp_oracle:
                             nat =>
                               (List[(nat, real)]) =>
                                 (List[(nat, List[(nat, real)])]) =>
                                   (List[(nat, real)]) =>
                                     Option[LP_Cert[List[(nat, real)]]],
                            lp_vm:
                              ((Boolean,
                                 (nat, (List[(nat, real)],
 List[(List[(nat, real)], (sense, real))]))),
                                (hashmap[var_code[(List[Option[nat]],
            (nat, Boolean)),
           List[Option[nat]]],
  nat],
                                  (nat, List[var_code[(List[Option[nat]],
                (nat, Boolean)),
               List[Option[nat]]]])))):
      lp_res[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                               List[Option[nat]]],
                      real]]
  =
  (solve_lp_am_empty_am_update_id_am_invar_am_empty_id_am_update_uu[(hashmap[var_code[(List[Option[nat]],
        (nat, Boolean)),
       List[Option[nat]]],
                                      nat],
                              (nat, List[var_code[(List[Option[nat]],
            (nat, Boolean)),
           List[Option[nat]]]]))](lp_oracle, lp_vm)
     match {
     case None =>
       Infeasible[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                                    List[Option[nat]]],
                           real]]()
     case Some(sol) =>
       {
         val ((_, (_, (c, _))), vm) =
           lp_vm:
             (((Boolean,
                 (nat, (List[(nat, real)],
                         List[(List[(nat, real)], (sense, real))]))),
               (hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                                  List[Option[nat]]],
                         nat],
                 (nat, List[var_code[(List[Option[nat]], (nat, Boolean)),
                                      List[Option[nat]]]]))))
         val n_to_v =
           nat_to_var[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
List[Option[nat]]],
                               nat],
                       nat,
                       var_code[(List[Option[nat]], (nat, Boolean)),
                                 List[Option[nat]]]](vm):
             (nat =>
               var_code[(List[Option[nat]], (nat, Boolean)), List[Option[nat]]])
         val nv =
           num_vars[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                                      List[Option[nat]]],
                             nat],
                     nat,
                     List[var_code[(List[Option[nat]], (nat, Boolean)),
                                    List[Option[nat]]]]](vm):
             nat
         val v_var =
           g_list_to_map_ahm_basic_ops[var_code[(List[Option[nat]],
          (nat, Boolean)),
         List[Option[nat]]],
real](map_filter[(nat, real),
                  (var_code[(List[Option[nat]], (nat, Boolean)),
                             List[Option[nat]]],
                    real)](((a: (nat, real)) =>
                             {
                               val (i, r) = a: ((nat, real));
                               (if (less_nat(i, nv))
                                 Some[(var_code[(List[Option[nat]],
          (nat, Boolean)),
         List[Option[nat]]],
real)]((n_to_v(i), r))
                                 else None)
                             }),
                            sol)):
             (hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                                List[Option[nat]]],
                       real]);
         Opt[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                               List[Option[nat]]],
                      real]](v_var,
                              fold[(nat, real),
                                    real](comp[real, real => real,
        (nat, real)](((a: real) => (b: real) => plus_reala(a, b)),
                      ((a: (nat, real)) =>
                        {
                          val (i, aa) = a: ((nat, real));
                          times_reala(lookup0_code_constr_map_ops[var_code[(List[Option[nat]],
                                     (nat, Boolean)),
                                    List[Option[nat]]]](n_to_v(i), v_var),
                                       aa)
                        })),
   c, zero_reala))
       }
   })

def var_to_nat_upd_ahm_basic_ops[A : equal : hashable](m:
                 (hashmap[A, nat], (nat, List[A])),
                v: A):
      ((hashmap[A, nat], (nat, List[A])), nat)
  =
  {
    val (ma, (n, to_v)) = m: ((hashmap[A, nat], (nat, List[A])));
    (ahm_lookup[A, nat](v, ma) match {
       case None => ((ahm_update[A, nat](v, n, ma), (Suc(n), v :: to_v)), n)
       case Some(a) => ((ma, (n, to_v)), a)
     })
  }

def ahm_iterateia[A : hashable, B, C](x0: hashmapa[A, B]):
      (C => Boolean) => (((A, B)) => C => C) => C => C
  =
  x0 match {
  case HashMapa(a, n) =>
    ((b: C => Boolean) => (c: ((A, B)) => C => C) => (d: C) =>
      ahm_iteratei_aux[A, B, C](a, b, c, d))
}

def ahm_iteratei[A : hashable, B, C](hm: hashmap[A, B]):
      (C => Boolean) => (((A, B)) => C => C) => C => C
  =
  ahm_iterateia[A, B, C](impl_of[A, B](hm))

def iteratei_bmap_op_list_it_ahm_basic_ops[A : hashable, B,
    C](s: hashmap[A, B]):
      (C => Boolean) => (((A, B)) => C => C) => C => C
  =
  ahm_iteratei[A, B, C](s)

def g_to_list_ahm_basic_ops[A : hashable, B](m: hashmap[A, B]): List[(A, B)] =
  (iteratei_bmap_op_list_it_ahm_basic_ops[A, B,
   List[(A, B)]](m)).apply(((_: List[(A, B)]) =>
                             true)).apply(((a: (A, B)) => (b: List[(A, B)]) =>
    a :: b)).apply(Nil)

def coeffs_to_nat_var_to_nat_upd_ahm_basic_ops_constr_map_ops(cs:
                        hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
  List[Option[nat]]],
                                 real],
                       vm: (hashmap[var_code[(List[Option[nat]],
       (nat, Boolean)),
      List[Option[nat]]],
                                     nat],
                             (nat, List[var_code[(List[Option[nat]],
           (nat, Boolean)),
          List[Option[nat]]]]))):
      (List[(nat, real)],
        (hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                           List[Option[nat]]],
                  nat],
          (nat, List[var_code[(List[Option[nat]], (nat, Boolean)),
                               List[Option[nat]]]])))
  =
  fold[(var_code[(List[Option[nat]], (nat, Boolean)), List[Option[nat]]], real),
        (List[(nat, real)],
          (hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                             List[Option[nat]]],
                    nat],
            (nat, List[var_code[(List[Option[nat]], (nat, Boolean)),
                                 List[Option[nat]]]])))](((a:
                     (var_code[(List[Option[nat]], (nat, Boolean)),
                                List[Option[nat]]],
                       real))
                    =>
                   {
                     val (v, c) =
                       a: ((var_code[(List[Option[nat]], (nat, Boolean)),
                                      List[Option[nat]]],
                            real));
                     ((aa: (List[(nat, real)],
                             (hashmap[var_code[(List[Option[nat]],
         (nat, Boolean)),
        List[Option[nat]]],
                                       nat],
                               (nat, List[var_code[(List[Option[nat]],
             (nat, Boolean)),
            List[Option[nat]]]]))))
                        =>
                       {
                         val (csa, vma) =
                           aa: ((List[(nat, real)],
                                 (hashmap[var_code[(List[Option[nat]],
             (nat, Boolean)),
            List[Option[nat]]],
   nat],
                                   (nat, List[var_code[(List[Option[nat]],
                 (nat, Boolean)),
                List[Option[nat]]]]))))
                         val (vmb, i) =
                           var_to_nat_upd_ahm_basic_ops[var_code[(List[Option[nat]],
                           (nat, Boolean)),
                          List[Option[nat]]]](vma, v):
                             (((hashmap[var_code[(List[Option[nat]],
           (nat, Boolean)),
          List[Option[nat]]],
 nat],
                                 (nat, List[var_code[(List[Option[nat]],
               (nat, Boolean)),
              List[Option[nat]]]])),
                               nat));
                         ((i, c) :: csa, vmb)
                       })
                   }),
                  g_to_list_ahm_basic_ops[var_code[(List[Option[nat]],
             (nat, Boolean)),
            List[Option[nat]]],
   real](cs),
                  (Nil, vm))

def constr_to_nat_var_to_nat_upd_ahm_basic_ops_constr_map_ops(c:
                        Constr_Code[hashmap[var_code[(List[Option[nat]],
               (nat, Boolean)),
              List[Option[nat]]],
     real]],
                       vm: (hashmap[var_code[(List[Option[nat]],
       (nat, Boolean)),
      List[Option[nat]]],
                                     nat],
                             (nat, List[var_code[(List[Option[nat]],
           (nat, Boolean)),
          List[Option[nat]]]]))):
      ((List[(nat, real)], (sense, real)),
        (hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                           List[Option[nat]]],
                  nat],
          (nat, List[var_code[(List[Option[nat]], (nat, Boolean)),
                               List[Option[nat]]]])))
  =
  (c match {
     case Constr_Le(cs, r) =>
       {
         val (coeffs_nat, a) =
           coeffs_to_nat_var_to_nat_upd_ahm_basic_ops_constr_map_ops(cs, vm):
             ((List[(nat, real)],
               (hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                                  List[Option[nat]]],
                         nat],
                 (nat, List[var_code[(List[Option[nat]], (nat, Boolean)),
                                      List[Option[nat]]]]))));
         ((coeffs_nat, (Leq(), r)), a)
       }
     case Constr_Eq(cs, r) =>
       {
         val (coeffs_nat, a) =
           coeffs_to_nat_var_to_nat_upd_ahm_basic_ops_constr_map_ops(cs, vm):
             ((List[(nat, real)],
               (hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                                  List[Option[nat]]],
                         nat],
                 (nat, List[var_code[(List[Option[nat]], (nat, Boolean)),
                                      List[Option[nat]]]]))));
         ((coeffs_nat, (Eqa(), r)), a)
       }
   })

def constrs_to_nat_var_to_nat_upd_ahm_basic_ops_constr_map_ops(cs:
                         List[Constr_Code[hashmap[var_code[(List[Option[nat]],
                     (nat, Boolean)),
                    List[Option[nat]]],
           real]]],
                        vm: (hashmap[var_code[(List[Option[nat]],
        (nat, Boolean)),
       List[Option[nat]]],
                                      nat],
                              (nat, List[var_code[(List[Option[nat]],
            (nat, Boolean)),
           List[Option[nat]]]]))):
      (List[(List[(nat, real)], (sense, real))],
        (hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                           List[Option[nat]]],
                  nat],
          (nat, List[var_code[(List[Option[nat]], (nat, Boolean)),
                               List[Option[nat]]]])))
  =
  fold[Constr_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                                     List[Option[nat]]],
                            real]],
        (List[(List[(nat, real)], (sense, real))],
          (hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                             List[Option[nat]]],
                    nat],
            (nat, List[var_code[(List[Option[nat]], (nat, Boolean)),
                                 List[Option[nat]]]])))](((c:
                     Constr_Code[hashmap[var_code[(List[Option[nat]],
            (nat, Boolean)),
           List[Option[nat]]],
  real]])
                    =>
                   (a: (List[(List[(nat, real)], (sense, real))],
                         (hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
    List[Option[nat]]],
                                   nat],
                           (nat, List[var_code[(List[Option[nat]],
         (nat, Boolean)),
        List[Option[nat]]]]))))
                     =>
                   {
                     val (csa, vma) =
                       a: ((List[(List[(nat, real)], (sense, real))],
                            (hashmap[var_code[(List[Option[nat]],
        (nat, Boolean)),
       List[Option[nat]]],
                                      nat],
                              (nat, List[var_code[(List[Option[nat]],
            (nat, Boolean)),
           List[Option[nat]]]]))))
                     val (c_nat, aa) =
                       constr_to_nat_var_to_nat_upd_ahm_basic_ops_constr_map_ops(c,
  vma):
                         (((List[(nat, real)], (sense, real)),
                           (hashmap[var_code[(List[Option[nat]],
       (nat, Boolean)),
      List[Option[nat]]],
                                     nat],
                             (nat, List[var_code[(List[Option[nat]],
           (nat, Boolean)),
          List[Option[nat]]]]))));
                     (c_nat :: csa, aa)
                   }),
                  cs, (Nil, vm))

def empty_var_map_ahm_basic_ops[A : hashable, B : zero, C]:
      (hashmap[A, nat], (B, List[C]))
  =
  (ahm_empty[A, nat].apply(()), (zero[B], Nil))

def lp_to_nat_empty_var_map_ahm_basic_ops_num_vars_var_to_nat_upd_ahm_basic_ops_constr_map_ops(cs:
                 List[Constr_Code[hashmap[var_code[(List[Option[nat]],
             (nat, Boolean)),
            List[Option[nat]]],
   real]]],
                obj: hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                                       List[Option[nat]]],
                              real]):
      ((Boolean,
         (nat, (List[(nat, real)], List[(List[(nat, real)], (sense, real))]))),
        (hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                           List[Option[nat]]],
                  nat],
          (nat, List[var_code[(List[Option[nat]], (nat, Boolean)),
                               List[Option[nat]]]])))
  =
  {
    val (obj_nat, vm) =
      coeffs_to_nat_var_to_nat_upd_ahm_basic_ops_constr_map_ops(obj,
                         empty_var_map_ahm_basic_ops[var_code[(List[Option[nat]],
                        (nat, Boolean)),
                       List[Option[nat]]],
              nat,
              var_code[(List[Option[nat]], (nat, Boolean)),
                        List[Option[nat]]]]):
        ((List[(nat, real)],
          (hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                             List[Option[nat]]],
                    nat],
            (nat, List[var_code[(List[Option[nat]], (nat, Boolean)),
                                 List[Option[nat]]]]))))
    val (cs_nat, vma) =
      constrs_to_nat_var_to_nat_upd_ahm_basic_ops_constr_map_ops(cs, vm):
        ((List[(List[(nat, real)], (sense, real))],
          (hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                             List[Option[nat]]],
                    nat],
            (nat, List[var_code[(List[Option[nat]], (nat, Boolean)),
                                 List[Option[nat]]]]))));
    ((true,
       (num_vars[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                                   List[Option[nat]]],
                          nat],
                  nat,
                  List[var_code[(List[Option[nat]], (nat, Boolean)),
                                 List[Option[nat]]]]](vma),
         (obj_nat, cs_nat))),
      vma)
  }

def minimize_empty_var_map_ahm_basic_ops_num_vars_var_to_nat_upd_ahm_basic_ops_am_empty_am_update_id_am_invar_am_empty_id_constr_map_ops_am_update_nat_to_var_uu(lp_oracle:
   nat =>
     (List[(nat, real)]) =>
       (List[(nat, List[(nat, real)])]) =>
         (List[(nat, real)]) => Option[LP_Cert[List[(nat, real)]]],
  lp: LP_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                                List[Option[nat]]],
                       real]]):
      lp_res[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                               List[Option[nat]]],
                      real]]
  =
  {
    val (LP_Codea(obj, cs)) =
      lp: (LP_Code[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                                     List[Option[nat]]],
                            real]])
    val a =
      lp_to_nat_empty_var_map_ahm_basic_ops_num_vars_var_to_nat_upd_ahm_basic_ops_constr_map_ops(cs,
                  obj):
        (((Boolean,
            (nat, (List[(nat, real)],
                    List[(List[(nat, real)], (sense, real))]))),
          (hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                             List[Option[nat]]],
                    nat],
            (nat, List[var_code[(List[Option[nat]], (nat, Boolean)),
                                 List[Option[nat]]]]))));
    lp_minimize_num_vars_am_empty_am_update_id_am_invar_am_empty_id_constr_map_ops_am_update_nat_to_var_uu(lp_oracle,
                            a)
  }

def lp_sol_code_vec_ops_uu_set_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_constr_map_ops_minimize_empty_var_map_ahm_basic_ops_num_vars_var_to_nat_upd_ahm_basic_ops_am_empty_am_update_id_am_invar_am_empty_id_constr_map_ops_am_update_nat_to_var_uu_scoped_ereal_ops_uu_ste_ops_scoped_real_ops_uu_uu_uu(api_input:
         api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
        lp_oracle:
          nat =>
            (List[(nat, real)]) =>
              (List[(nat, List[(nat, real)])]) =>
                (List[(nat, real)]) => Option[LP_Cert[List[(nat, real)]]],
        dec_pol_code: List[((Array.T[nat], nat), nat)],
        g_cache: nat => nat => (((Array.T[nat], nat)) => real, nat)):
      (hashmap[var_code[(List[Option[nat]], (nat, Boolean)), List[Option[nat]]],
                real],
        real)
  =
  (minimize_empty_var_map_ahm_basic_ops_num_vars_var_to_nat_upd_ahm_basic_ops_am_empty_am_update_id_am_invar_am_empty_id_constr_map_ops_am_update_nat_to_var_uu(lp_oracle,
 lp_code_vec_ops_uu_set_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_constr_map_ops_scoped_ereal_ops_uu_ste_ops_scoped_real_ops_uu_uu_uu(api_input,
    dec_pol_code, g_cache))
     match {
     case Opt(a, b) => (a, b)
     case Infeasible() =>
       default_sol_vec_ops_uu_set_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_constr_map_ops_scoped_ereal_ops_uu_ste_ops_scoped_real_ops_uu_uu_uu(api_input,
              dec_pol_code, g_cache)
     case Unbounded() =>
       default_sol_vec_ops_uu_set_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_constr_map_ops_scoped_ereal_ops_uu_ste_ops_scoped_real_ops_uu_uu_uu(api_input,
              dec_pol_code, g_cache)
   })

def upd_weights_code_vec_ops_uu_set_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_constr_map_ops_minimize_empty_var_map_ahm_basic_ops_num_vars_var_to_nat_upd_ahm_basic_ops_am_empty_am_update_id_am_invar_am_empty_id_constr_map_ops_am_update_nat_to_var_uu_scoped_ereal_ops_uu_ste_ops_scoped_real_ops_uu_uu_uu(api_input:
              api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
             lp_oracle:
               nat =>
                 (List[(nat, real)]) =>
                   (List[(nat, List[(nat, real)])]) =>
                     (List[(nat, real)]) => Option[LP_Cert[List[(nat, real)]]],
             dec_pol_code: List[((Array.T[nat], nat), nat)],
             g_cache: nat => nat => (((Array.T[nat], nat)) => real, nat)):
      nat => real
  =
  {
    val sol =
      fst[hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                            List[Option[nat]]],
                   real],
           real](lp_sol_code_vec_ops_uu_set_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_constr_map_ops_minimize_empty_var_map_ahm_basic_ops_num_vars_var_to_nat_upd_ahm_basic_ops_am_empty_am_update_id_am_invar_am_empty_id_constr_map_ops_am_update_nat_to_var_uu_scoped_ereal_ops_uu_ste_ops_scoped_real_ops_uu_uu_uu(api_input,
                     lp_oracle, dec_pol_code, g_cache)):
        (hashmap[var_code[(List[Option[nat]], (nat, Boolean)),
                           List[Option[nat]]],
                  real])
    val a =
      of_fun[real](((i: nat) =>
                     real_of_ereal(ereala(lookup0_code_constr_map_ops[var_code[(List[Option[nat]],
 (nat, Boolean)),
List[Option[nat]]]](var_w[(List[Option[nat]], (nat, Boolean)),
                           List[Option[nat]]](i),
                     sol)))),
                    api_input_h_dim_code[nat, (DiffArray.T[Option[real]], nat),
  Unit](api_input)):
        (Array.T[real]);
    ((b: nat) => sub[real](a, b))
  }

def update_weights_code_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_real_ops_uu_vec_ops_uu_set_ops_ste_ops_constr_map_ops_scoped_ereal_ops_uu_minimize_empty_var_map_ahm_basic_ops_num_vars_var_to_nat_upd_ahm_basic_ops_am_empty_am_update_id_am_invar_am_empty_id_constr_map_ops_am_update_nat_to_var_uu(api_input:
           api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
          lp_oracle:
            nat =>
              (List[(nat, real)]) =>
                (List[(nat, List[(nat, real)])]) =>
                  (List[(nat, real)]) => Option[LP_Cert[List[(nat, real)]]],
          g: nat => nat => (((Array.T[nat], nat)) => real, nat),
          pol: List[((Array.T[nat], nat), nat)]):
      nat => real
  =
  upd_weights_code_vec_ops_uu_set_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_constr_map_ops_minimize_empty_var_map_ahm_basic_ops_num_vars_var_to_nat_upd_ahm_basic_ops_am_empty_am_update_id_am_invar_am_empty_id_constr_map_ops_am_update_nat_to_var_uu_scoped_ereal_ops_uu_ste_ops_scoped_real_ops_uu_uu_uu(api_input,
           lp_oracle, pol, g)

def api_input_effects_code[A, B, C](x0: api_input_ext[A, B, C]): nat => A = x0
  match {
  case api_input_exta(api_input_dims, api_input_doms, api_input_t_max_code,
                       api_input_epsilon_code, api_input_rewards_code_fn,
                       api_input_rewards_scope_code, api_input_reward_dim_code,
                       api_input_actions_code, api_input_d_code,
                       api_input_transitions_code_fn,
                       api_input_transitions_scopes_code, api_input_l_code,
                       api_input_h_code_fn, api_input_h_scope_code,
                       api_input_h_dim_code, api_input_effects_code, more)
    => api_input_effects_code
}

def g_from_list_aux_bs_basic_ops(y: nat, x1: List[nat]): nat = (y, x1) match {
  case (y, Nil) => y
  case (accs, x :: l) => g_from_list_aux_bs_basic_ops(set_bit_nat(x, accs), l)
}

def g_from_list_bs_basic_ops(l: List[nat]): nat =
  g_from_list_aux_bs_basic_ops(zero_nata, l)

def g_disjoint_bs_basic_ops(s1: nat, s2: nat): Boolean =
  g_ball_bs_basic_ops(s1, ((x: nat) => ! (bit_nat(s2, x))))

def I_a_code_scoped_real_ops_uu_set_ops_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_api_input_effects_code_uu(api_input:
            api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
           a: nat):
      nat
  =
  g_from_list_bs_basic_ops(filter[nat](((i: nat) =>
 ! (g_disjoint_bs_basic_ops((api_input_effects_code[nat,
             (DiffArray.T[Option[real]], nat), Unit](api_input)).apply(a),
                             (scoped_fn_op_scope[(((Array.T[nat], nat)) => real,
           nat),
          (Array.T[nat], nat), real, nat,
          scoped_fn_real_ops_ext[(((Array.T[nat], nat)) => real, nat),
                                  Unit]](scoped_real_ops_uua(api_input))).apply((h_code_scoped_real_ops_uu_vec_ops_uu_uu(api_input)).apply(i))))),
upt.apply(zero_nata).apply(api_input_h_dim_code[nat,
         (DiffArray.T[Option[real]], nat), Unit](api_input))))

def scoped_base_apply_vec_ops_uub(api_input:
                                    api_input_ext[nat,
           (DiffArray.T[Option[real]], nat), Unit],
                                   x1: Scoped_Tree[(DiffArray.T[Option[real]],
             nat)],
                                   v: (Array.T[nat], nat)):
      (DiffArray.T[Option[real]], nat)
  =
  (api_input, x1, v) match {
  case (api_input, Scoped_Leaf(y), v) => y
  case (api_input, Scoped_Node(i, arr), v) =>
    {
      val j =
        (vec_op_idx[(Array.T[nat], nat), nat, nat,
                     Unit](vec_ops_uua(api_input))).apply(v).apply(i):
          nat
      val true =
        less_nat(j, length[Scoped_Tree[(DiffArray.T[Option[real]], nat)]](arr)):
          Boolean;
      scoped_base_apply_vec_ops_uub(api_input,
                                     sub[Scoped_Tree[(DiffArray.T[Option[real]],
               nat)]](arr, j),
                                     v)
    }
}

def scoped_eval_vec_ops_uu_set_ops_api_input_doms_uub(api_input:
                api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
               sf: (((Array.T[nat], nat)) => (DiffArray.T[Option[real]], nat),
                     nat)):
      (((Array.T[nat], nat)) => (DiffArray.T[Option[real]], nat), nat)
  =
  {
    val (f, s) =
      sf: ((((Array.T[nat], nat)) => (DiffArray.T[Option[real]], nat), nat))
    val arr =
      eval_list_vec_ops_uu_api_input_doms_uu[(DiffArray.T[Option[real]],
       nat)](api_input, f,
              vec_op_empty[(Array.T[nat], nat), nat, nat,
                            Unit](vec_ops_uua(api_input)),
              g_to_list_bs_basic_ops(s)):
        (Scoped_Tree[(DiffArray.T[Option[real]], nat)])
    val fa =
      ((a: (Array.T[nat], nat)) =>
        scoped_base_apply_vec_ops_uub(api_input, arr, a)):
        (((Array.T[nat], nat)) => (DiffArray.T[Option[real]], nat));
    (fa, s)
  }

def scoped_fn_ops_vec_ops_uu_set_ops_api_input_doms_uub(api_input:
                  api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit]):
      scoped_fn_basic_ops_ext[(((Array.T[nat], nat)) =>
                                 (DiffArray.T[Option[real]], nat),
                                nat),
                               (Array.T[nat], nat),
                               (DiffArray.T[Option[real]], nat), nat, Unit]
  =
  scoped_fn_basic_ops_exta[(((Array.T[nat], nat)) =>
                              (DiffArray.T[Option[real]], nat),
                             nat),
                            (Array.T[nat], nat),
                            (DiffArray.T[Option[real]], nat), nat,
                            Unit](((a: (((Array.T[nat], nat)) =>
  (DiffArray.T[Option[real]], nat),
 nat))
                                     =>
                                    (b: (Array.T[nat], nat)) =>
                                    scoped_apply[(Array.T[nat], nat),
          (DiffArray.T[Option[real]], nat), nat](a, b)),
                                   ((f: (((Array.T[nat], nat)) =>
   (DiffArray.T[Option[real]], nat),
  nat))
                                      =>
                                     bs_alpha(scoped_scope[(Array.T[nat], nat),
                    (DiffArray.T[Option[real]], nat), nat](f))),
                                   ((a: (((Array.T[nat], nat)) =>
   (DiffArray.T[Option[real]], nat),
  nat))
                                      =>
                                     scoped_scope[(Array.T[nat], nat),
           (DiffArray.T[Option[real]], nat), nat](a)),
                                   ((a: nat) =>
                                     (b:
((Array.T[nat], nat)) => (DiffArray.T[Option[real]], nat))
                                       =>
                                     scoped_from_fn[nat, (Array.T[nat], nat),
             (DiffArray.T[Option[real]], nat)](a, b)),
                                   ((a: (((Array.T[nat], nat)) =>
   (DiffArray.T[Option[real]], nat),
  nat))
                                      =>
                                     scoped_invar_vec_ops_uu_set_opsb[(DiffArray.T[Option[real]],
                                nat)](api_input, a)),
                                   ((a: (((Array.T[nat], nat)) =>
   (DiffArray.T[Option[real]], nat),
  nat))
                                      =>
                                     (b: (Array.T[nat], nat)) =>
                                     scoped_inst_vec_ops_uu_set_opsb[(DiffArray.T[Option[real]],
                               nat)](api_input, a, b)),
                                   ((a: (((Array.T[nat], nat)) =>
   (DiffArray.T[Option[real]], nat),
  nat))
                                      =>
                                     scoped_eval_vec_ops_uu_set_ops_api_input_doms_uub(api_input,
        a)),
                                   ())

def scoped_pmf_ops_uua(api_input:
                         api_input_ext[nat, (DiffArray.T[Option[real]], nat),
Unit]):
      scoped_fn_basic_ops_ext[(((Array.T[nat], nat)) =>
                                 (DiffArray.T[Option[real]], nat),
                                nat),
                               (Array.T[nat], nat),
                               (DiffArray.T[Option[real]], nat), nat, Unit]
  =
  scoped_fn_ops_vec_ops_uu_set_ops_api_input_doms_uub(api_input)

def SP_scoped_tree_to_scoped_fn_scoped_pmf_ops_uu_vec_ops_uu(api_input:
                       api_input_ext[nat, (DiffArray.T[Option[real]], nat),
                                      Unit],
                      f: Scoped_Tree[(DiffArray.T[Option[real]], nat)], s: nat):
      (((Array.T[nat], nat)) => (DiffArray.T[Option[real]], nat), nat)
  =
  (scoped_fn_op_from_fn[(((Array.T[nat], nat)) =>
                           (DiffArray.T[Option[real]], nat),
                          nat),
                         (Array.T[nat], nat), (DiffArray.T[Option[real]], nat),
                         nat,
                         Unit](scoped_pmf_ops_uua(api_input))).apply(s).apply(((a:
  (Array.T[nat], nat))
 =>
scoped_tree_eval_vec_ops_uu[(DiffArray.T[Option[real]], nat)](api_input, f, a)))

def api_input_transitions_scopes_code[A, B, C](x0: api_input_ext[A, B, C]):
      nat => nat => A
  =
  x0 match {
  case api_input_exta(api_input_dims, api_input_doms, api_input_t_max_code,
                       api_input_epsilon_code, api_input_rewards_code_fn,
                       api_input_rewards_scope_code, api_input_reward_dim_code,
                       api_input_actions_code, api_input_d_code,
                       api_input_transitions_code_fn,
                       api_input_transitions_scopes_code, api_input_l_code,
                       api_input_h_code_fn, api_input_h_scope_code,
                       api_input_h_dim_code, api_input_effects_code, more)
    => api_input_transitions_scopes_code
}

def api_input_transitions_code_fn[A, B, C](x0: api_input_ext[A, B, C]):
      nat => nat => Scoped_Tree[B]
  =
  x0 match {
  case api_input_exta(api_input_dims, api_input_doms, api_input_t_max_code,
                       api_input_epsilon_code, api_input_rewards_code_fn,
                       api_input_rewards_scope_code, api_input_reward_dim_code,
                       api_input_actions_code, api_input_d_code,
                       api_input_transitions_code_fn,
                       api_input_transitions_scopes_code, api_input_l_code,
                       api_input_h_code_fn, api_input_h_scope_code,
                       api_input_h_dim_code, api_input_effects_code, more)
    => api_input_transitions_code_fn
}

def transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu(api_input:
                       api_input_ext[nat, (DiffArray.T[Option[real]], nat),
                                      Unit]):
      nat =>
        nat => (((Array.T[nat], nat)) => (DiffArray.T[Option[real]], nat), nat)
  =
  {
    val rs =
      of_fun[Array.T[((((Array.T[nat], nat)) =>
                         (DiffArray.T[Option[real]], nat),
                       nat))]](((a: nat) =>
                                 of_fun[(((Array.T[nat], nat)) =>
   (DiffArray.T[Option[real]], nat),
  nat)](((i: nat) =>
          {
            val act =
              (if (bit_nat((api_input_effects_code[nat,
            (DiffArray.T[Option[real]], nat), Unit](api_input)).apply(a),
                            i))
                a else api_input_d_code[nat, (DiffArray.T[Option[real]], nat),
 Unit](api_input)):
                nat;
            SP_scoped_tree_to_scoped_fn_scoped_pmf_ops_uu_vec_ops_uu(api_input,
                              (api_input_transitions_code_fn[nat,
                      (DiffArray.T[Option[real]], nat),
                      Unit](api_input)).apply(act).apply(i),
                              (api_input_transitions_scopes_code[nat,
                          (DiffArray.T[Option[real]], nat),
                          Unit](api_input)).apply(act).apply(i))
          }),
         api_input_dims[nat, (DiffArray.T[Option[real]], nat),
                         Unit](api_input))),
                                api_input_actions_code[nat,
                (DiffArray.T[Option[real]], nat), Unit](api_input)):
        (Array.T[(Array.T[((((Array.T[nat], nat)) =>
                              (DiffArray.T[Option[real]], nat),
                            nat))])]);
    ((a: nat) =>
      ((b: nat) =>
        sub[(((Array.T[nat], nat)) => (DiffArray.T[Option[real]], nat),
              nat)](sub[Array.T[((((Array.T[nat], nat)) =>
                                    (DiffArray.T[Option[real]], nat),
                                  nat))]](rs, a),
                     b)))
  }

def Gamma_a_code_scoped_pmf_ops_uu_set_ops_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu(api_input:
                      api_input_ext[nat, (DiffArray.T[Option[real]], nat),
                                     Unit],
                     a: nat, x: nat):
      nat
  =
  Union_sets_set_ops(map[nat, nat](((i: nat) =>
                                     (scoped_fn_op_scope[(((Array.T[nat],
                    nat)) =>
                    (DiffArray.T[Option[real]], nat),
                   nat),
                  (Array.T[nat], nat), (DiffArray.T[Option[real]], nat), nat,
                  Unit](scoped_pmf_ops_uua(api_input))).apply((transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu(api_input)).apply(a).apply(i))),
                                    g_to_list_bs_basic_ops(x)))

def Gamma_a_code_scoped_pmf_ops_uu_set_ops_api_input_d_code_uu_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu(api_input:
  api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
 a: nat, x: nat):
      nat
  =
  g_union_bs_basic_ops(Gamma_a_code_scoped_pmf_ops_uu_set_ops_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu(api_input,
a, x),
                        Gamma_a_code_scoped_pmf_ops_uu_set_ops_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu(api_input,
 api_input_d_code[nat, (DiffArray.T[Option[real]], nat), Unit](api_input), x))

def U_a_code_scoped_real_ops_uu_set_ops_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_d_code_uu(api_input:
                               api_input_ext[nat,
      (DiffArray.T[Option[real]], nat), Unit],
                              a: nat):
      nat
  =
  {
    val r_range =
      upt.apply(plus_nata((api_input_reward_dim_code[nat,
              (DiffArray.T[Option[real]], nat),
              Unit](api_input)).apply(api_input_d_code[nat,
                (DiffArray.T[Option[real]], nat), Unit](api_input)),
                           (if (equal_nata(api_input_d_code[nat,
                     (DiffArray.T[Option[real]], nat), Unit](api_input),
    api_input_d_code[nat, (DiffArray.T[Option[real]], nat), Unit](api_input)))
                             zero_nata
                             else (api_input_reward_dim_code[nat,
                      (DiffArray.T[Option[real]], nat),
                      Unit](api_input)).apply(api_input_d_code[nat,
                        (DiffArray.T[Option[real]], nat),
                        Unit](api_input))))).apply(plus_nata((api_input_reward_dim_code[nat,
         (DiffArray.T[Option[real]], nat), Unit](api_input)).apply(a),
                      (if (equal_nata(a, api_input_d_code[nat,
                   (DiffArray.T[Option[real]], nat), Unit](api_input)))
                        zero_nata
                        else (api_input_reward_dim_code[nat,
                 (DiffArray.T[Option[real]], nat),
                 Unit](api_input)).apply(api_input_d_code[nat,
                   (DiffArray.T[Option[real]], nat), Unit](api_input))))):
        (List[nat])
    val add_scope =
      ((i: nat) =>
        ((b: nat) =>
          g_union_bs_basic_ops((scoped_fn_op_scope[(((Array.T[nat], nat)) =>
              real,
             nat),
            (Array.T[nat], nat), real, nat,
            scoped_fn_real_ops_ext[(((Array.T[nat], nat)) => real, nat),
                                    Unit]](scoped_real_ops_uua(api_input))).apply((rewards_code_scoped_real_ops_uu_vec_ops_uu_uu(api_input)).apply(a).apply(i)),
                                b))):
        (nat => nat => nat);
    fold[nat, nat](add_scope, r_range, zero_nata)
  }

def T_a_code_scoped_real_ops_uu_scoped_pmf_ops_uu_set_ops_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_d_code_uu_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_api_input_effects_code_uu(api_input:
                                    api_input_ext[nat,
           (DiffArray.T[Option[real]], nat), Unit],
                                   a: nat):
      nat
  =
  {
    val ia_list =
      g_to_list_bs_basic_ops(I_a_code_scoped_real_ops_uu_set_ops_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_api_input_effects_code_uu(api_input,
                                    a)):
        (List[nat])
    val b =
      Union_sets_set_ops(map[nat, nat](((i: nat) =>
 Gamma_a_code_scoped_pmf_ops_uu_set_ops_api_input_d_code_uu_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu(api_input,
                                      a, (scoped_fn_op_scope[(((Array.T[nat],
                        nat)) =>
                        real,
                       nat),
                      (Array.T[nat], nat), real, nat,
                      scoped_fn_real_ops_ext[(((Array.T[nat], nat)) => real,
       nat),
      Unit]](scoped_real_ops_uua(api_input))).apply((h_code_scoped_real_ops_uu_vec_ops_uu_uu(api_input)).apply(i)))),
ia_list)):
        nat;
    g_union_bs_basic_ops(U_a_code_scoped_real_ops_uu_set_ops_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_d_code_uu(api_input,
           a),
                          b)
  }

def sum_list[A : monoid_add](xs: List[A]): A =
  (foldr[A, A](((a: A) => (b: A) => plus[A](a, b)), xs)).apply(zero[A])

def R_a_code_scoped_real_ops_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_d_code_uu(api_input:
                       api_input_ext[nat, (DiffArray.T[Option[real]], nat),
                                      Unit],
                      a: nat, x: (Array.T[nat], nat)):
      real
  =
  sum_list[real](map[nat, real](((i: nat) =>
                                  (scoped_fn_op_alpha[(((Array.T[nat], nat)) =>
                 real,
                nat),
               (Array.T[nat], nat), real, nat,
               scoped_fn_real_ops_ext[(((Array.T[nat], nat)) => real, nat),
                                       Unit]](scoped_real_ops_uua(api_input))).apply((rewards_code_scoped_real_ops_uu_vec_ops_uu_uu(api_input)).apply(a).apply(i)).apply(x)),
                                 upt.apply(plus_nata((api_input_reward_dim_code[nat,
 (DiffArray.T[Option[real]], nat),
 Unit](api_input)).apply(api_input_d_code[nat, (DiffArray.T[Option[real]], nat),
   Unit](api_input)),
              (if (equal_nata(api_input_d_code[nat,
        (DiffArray.T[Option[real]], nat), Unit](api_input),
                               api_input_d_code[nat,
         (DiffArray.T[Option[real]], nat), Unit](api_input)))
                zero_nata
                else (api_input_reward_dim_code[nat,
         (DiffArray.T[Option[real]], nat),
         Unit](api_input)).apply(api_input_d_code[nat,
           (DiffArray.T[Option[real]], nat),
           Unit](api_input))))).apply(plus_nata((api_input_reward_dim_code[nat,
                                    (DiffArray.T[Option[real]], nat),
                                    Unit](api_input)).apply(a),
         (if (equal_nata(a, api_input_d_code[nat,
      (DiffArray.T[Option[real]], nat), Unit](api_input)))
           zero_nata
           else (api_input_reward_dim_code[nat,
    (DiffArray.T[Option[real]], nat),
    Unit](api_input)).apply(api_input_d_code[nat,
      (DiffArray.T[Option[real]], nat), Unit](api_input)))))))

def set_sum_set_ops[A : plus : zero](x: nat, f: nat => A): A =
  (iteratei_set_op_list_it_set_ops[A](x)).apply(((_: A) =>
          true)).apply(((p: nat) =>
                         ((a: A) => plus[A](f(p), a)))).apply(zero[A])

def bonus_code_scoped_real_ops_uu_set_ops_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_d_code_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_api_input_effects_code_uu_uu_uu(api_input:
                             api_input_ext[nat,
    (DiffArray.T[Option[real]], nat), Unit],
                            g_cache:
                              nat =>
                                nat => (((Array.T[nat], nat)) => real, nat),
                            w_code: nat => real, a: nat,
                            x: (Array.T[nat], nat)):
      real
  =
  plus_reala(R_a_code_scoped_real_ops_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_d_code_uu(api_input,
                               a, x),
              times_reala(api_input_l_code[nat,
    (DiffArray.T[Option[real]], nat), Unit](api_input),
                           set_sum_set_ops[real](I_a_code_scoped_real_ops_uu_set_ops_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_api_input_effects_code_uu(api_input,
                a),
          ((i: nat) =>
            times_reala(w_code(i),
                         minus_reala((scoped_fn_op_alpha[(((Array.T[nat],
                    nat)) =>
                    real,
                   nat),
                  (Array.T[nat], nat), real, nat,
                  scoped_fn_real_ops_ext[(((Array.T[nat], nat)) => real, nat),
  Unit]](scoped_real_ops_uua(api_input))).apply((g_cache(i))(a)).apply(x),
                                      (scoped_fn_op_alpha[(((Array.T[nat],
                     nat)) =>
                     real,
                    nat),
                   (Array.T[nat], nat), real, nat,
                   scoped_fn_real_ops_ext[(((Array.T[nat], nat)) => real, nat),
   Unit]](scoped_real_ops_uua(api_input))).apply((g_cache(i))(api_input_d_code[nat,
(DiffArray.T[Option[real]], nat), Unit](api_input))).apply(x)))))))

def dec_list_act_code_scoped_real_ops_uu_scoped_pmf_ops_uu_vec_ops_uu_set_ops_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_d_code_uu_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_api_input_effects_code_uu_uu_uu(api_input:
                    api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
                   g_cache: nat => nat => (((Array.T[nat], nat)) => real, nat),
                   w_code: nat => real, a: nat):
      List[((Array.T[nat], nat), (nat, real))]
  =
  {
    val ta =
      T_a_code_scoped_real_ops_uu_scoped_pmf_ops_uu_set_ops_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_d_code_uu_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_api_input_effects_code_uu(api_input,
                                     a):
        nat
    val ts =
      assignments_impl_vec_ops_uu_set_ops_api_input_doms_uu(api_input, ta):
        (List[(Array.T[nat], nat)])
    val tsa =
      map_filter[(Array.T[nat], nat),
                  ((Array.T[nat], nat),
                    (nat, real))](((t: (Array.T[nat], nat)) =>
                                    {
                                      val b =
bonus_code_scoped_real_ops_uu_set_ops_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_d_code_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_api_input_effects_code_uu_uu_uu(api_input,
                        g_cache, w_code, a, t):
  real;
                                      (if (less_real(zero_reala, b))
Some[((Array.T[nat], nat), (nat, real))]((t, (a, b))) else None)
                                    }),
                                   ts):
        (List[((Array.T[nat], nat), (nat, real))]);
    tsa
  }

def actions_nondef_code_api_input_actions_code_uu_api_input_d_code_uu(api_input:
                                api_input_ext[nat,
       (DiffArray.T[Option[real]], nat), Unit]):
      List[nat]
  =
  remove1[nat](api_input_d_code[nat, (DiffArray.T[Option[real]], nat),
                                 Unit](api_input),
                upt.apply(zero_nata).apply(api_input_actions_code[nat,
                           (DiffArray.T[Option[real]], nat), Unit](api_input)))

def consistent_code_vec_ops_uu_set_ops(api_input:
 api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
x: (Array.T[nat], nat), t: (Array.T[nat], nat)):
      Boolean
  =
  g_ball_bs_basic_ops((vec_op_scope[(Array.T[nat], nat), nat, nat,
                                     Unit](vec_ops_uua(api_input))).apply(t),
                       ((i: nat) =>
                         equal_nata((vec_op_idx[(Array.T[nat], nat), nat, nat,
         Unit](vec_ops_uua(api_input))).apply(x).apply(i),
                                     (vec_op_idx[(Array.T[nat], nat), nat, nat,
          Unit](vec_ops_uua(api_input))).apply(t).apply(i))))

def g_subset_bs_basic_ops(s1: nat, s2: nat): Boolean =
  g_ball_bs_basic_ops(s1, ((a: nat) => bit_nat(s2, a)))

def dec_list_pol_filter_aux_code_vec_ops_uu_set_ops[A](api_input:
                 api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
                x: set[(Array.T[nat], nat)],
                xa2: List[((Array.T[nat], nat), A)]):
      List[((Array.T[nat], nat), A)]
  =
  (api_input, x, xa2) match {
  case (api_input, x, Nil) => Nil
  case (api_input, x, (t, a) :: xs) =>
    (if (Ball[(Array.T[nat],
                nat)](x, ((xa: (Array.T[nat], nat)) =>
                           ! (g_subset_bs_basic_ops((vec_op_scope[(Array.T[nat],
                            nat),
                           nat, nat, Unit](vec_ops_uua(api_input))).apply(xa),
             (vec_op_scope[(Array.T[nat], nat), nat, nat,
                            Unit](vec_ops_uua(api_input))).apply(t))) ||
                             ! (consistent_code_vec_ops_uu_set_ops(api_input, t,
                            xa)))))
      (t, a) ::
        dec_list_pol_filter_aux_code_vec_ops_uu_set_ops[A](api_input,
                    insert[(Array.T[nat], nat)](t, x), xs)
      else dec_list_pol_filter_aux_code_vec_ops_uu_set_ops[A](api_input, x, xs))
}

def size_list[A]: (List[A]) => nat =
  ((a: List[A]) => gen_length[A](zero_nata, a))

def part[A, B : linorder](f: A => B, pivot: B, x2: List[A]):
      (List[A], (List[A], List[A]))
  =
  (f, pivot, x2) match {
  case (f, pivot, x :: xs) =>
    {
      val (lts, (eqs, gts)) =
        part[A, B](f, pivot, xs): ((List[A], (List[A], List[A])))
      val xa = f(x): B;
      (if (less[B](xa, pivot)) (x :: lts, (eqs, gts))
        else (if (less[B](pivot, xa)) (lts, (eqs, x :: gts))
               else (lts, (x :: eqs, gts))))
    }
  case (f, pivot, Nil) => (Nil, (Nil, Nil))
}

def sort_key[A, B : linorder](f: A => B, xs: List[A]): List[A] =
  (xs match {
     case Nil => Nil
     case List(_) => xs
     case List(x, y) => (if (less_eq[B](f(x), f(y))) xs else List(y, x))
     case _ :: _ :: _ :: _ =>
       {
         val (lts, (eqs, gts)) =
           part[A, B](f, f(nth[A](xs, divide_nata(size_list[A].apply(xs),
           nat_of_integer(BigInt(2))))),
                       xs):
             ((List[A], (List[A], List[A])));
         sort_key[A, B](f, lts) ++ (eqs ++ sort_key[A, B](f, gts))
       }
   })

def sort_dec_list_code[A, B, C : uminus : linorder]:
      (List[(A, (B, C))]) => List[(A, (B, C))]
  =
  ((a: List[(A, (B, C))]) =>
    sort_key[(A, (B, C)),
              C](((aa: (A, (B, C))) => {
 val (_, (_, ab)) = aa: ((A, (B, C)));
 uminus[C](ab)
                                       }),
                  a))

def set_impl_choose2(x: set_impla, y: set_impla): set_impla = (x, y) match {
  case (set_Monad(), set_Monad()) => set_Monad()
  case (set_RBT(), set_RBT()) => set_RBT()
  case (set_DList(), set_DList()) => set_DList()
  case (set_Collect(), set_Collect()) => set_Collect()
  case (x, y) => set_Choose()
}

def set_impl_prod[A : set_impl, B : set_impl]: phantom[(A, B), set_impla] =
  phantoma[set_impla,
            (A, B)](set_impl_choose2(of_phantom[A, set_impla](set_impl[A]),
                                      of_phantom[B, set_impla](set_impl[B])))

def dec_list_pol_code_scoped_real_ops_uu_scoped_pmf_ops_uu_vec_ops_uu_set_ops_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_actions_code_uu_api_input_d_code_uu_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_api_input_effects_code_uu_uu_uu(api_input:
      api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
     g_cache: nat => nat => (((Array.T[nat], nat)) => real, nat),
     w_code: nat => real):
      List[((Array.T[nat], nat), nat)]
  =
  {
    val pi_unsorted =
      (vec_op_empty[(Array.T[nat], nat), nat, nat,
                     Unit](vec_ops_uua(api_input)),
        (api_input_d_code[nat, (DiffArray.T[Option[real]], nat),
                           Unit](api_input),
          zero_reala)) ::
        maps[nat, ((Array.T[nat], nat),
                    (nat, real))](((a: nat) =>
                                    dec_list_act_code_scoped_real_ops_uu_scoped_pmf_ops_uu_vec_ops_uu_set_ops_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_d_code_uu_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_api_input_effects_code_uu_uu_uu(api_input,
           g_cache, w_code, a)),
                                   actions_nondef_code_api_input_actions_code_uu_api_input_d_code_uu(api_input)):
        (List[((Array.T[nat], nat), (nat, real))])
    val pi_sorted =
      sort_dec_list_code[(Array.T[nat], nat), nat, real].apply(pi_unsorted):
        (List[((Array.T[nat], nat), (nat, real))])
    val pi =
      map[((Array.T[nat], nat), (nat, real)),
           ((Array.T[nat], nat),
             nat)](((a: ((Array.T[nat], nat), (nat, real))) =>
                     {
                       val (t, (aa, _)) =
                         a: (((Array.T[nat], nat), (nat, real)));
                       (t, aa)
                     }),
                    pi_sorted):
        (List[((Array.T[nat], nat), nat)])
    val pia =
      dec_list_pol_filter_aux_code_vec_ops_uu_set_ops[nat](api_input,
                    set_empty[(Array.T[nat],
                                nat)](of_phantom[(Array.T[nat], nat),
          set_impla](set_impl_prod[Array.T[nat], nat])),
                    pi):
        (List[((Array.T[nat], nat), nat)]);
    pia
  }

def update_dec_list_code_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_actions_code_uu_api_input_d_code_uu_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_api_input_effects_code_uu_scoped_real_ops_uu_scoped_pmf_ops_uu_vec_ops_uu_set_ops(api_input:
   api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit]):
      (nat => nat => (((Array.T[nat], nat)) => real, nat)) =>
        (nat => real) => List[((Array.T[nat], nat), nat)]
  =
  ((a: nat => nat => (((Array.T[nat], nat)) => real, nat)) =>
    (b: nat => real) =>
    dec_list_pol_code_scoped_real_ops_uu_scoped_pmf_ops_uu_vec_ops_uu_set_ops_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_actions_code_uu_api_input_d_code_uu_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_api_input_effects_code_uu_uu_uu(api_input,
     a, b))

def body_code_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_actions_code_uu_api_input_d_code_uu_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_api_input_effects_code_uu_scoped_real_ops_uu_scoped_pmf_ops_uu_vec_ops_uu_set_ops_ste_ops_constr_map_ops_scoped_ereal_ops_uu_minimize_empty_var_map_ahm_basic_ops_num_vars_var_to_nat_upd_ahm_basic_ops_am_empty_am_update_id_am_invar_am_empty_id_constr_map_ops_am_update_nat_to_var_uu(api_input:
                            api_input_ext[nat, (DiffArray.T[Option[real]], nat),
   Unit],
                           lp_oracle:
                             nat =>
                               (List[(nat, real)]) =>
                                 (List[(nat, List[(nat, real)])]) =>
                                   (List[(nat, real)]) =>
                                     Option[LP_Cert[List[(nat, real)]]],
                           g: nat =>
                                nat => (((Array.T[nat], nat)) => real, nat),
                           p: List[((Array.T[nat], nat), nat)]):
      (List[((Array.T[nat], nat), nat)], nat => real)
  =
  {
    val w =
      update_weights_code_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_real_ops_uu_vec_ops_uu_set_ops_ste_ops_constr_map_ops_scoped_ereal_ops_uu_minimize_empty_var_map_ahm_basic_ops_num_vars_var_to_nat_upd_ahm_basic_ops_am_empty_am_update_id_am_invar_am_empty_id_constr_map_ops_am_update_nat_to_var_uu(api_input,
            lp_oracle, g, p):
        (nat => real)
    val pa =
      (update_dec_list_code_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_actions_code_uu_api_input_d_code_uu_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_api_input_effects_code_uu_scoped_real_ops_uu_scoped_pmf_ops_uu_vec_ops_uu_set_ops(api_input)).apply(g).apply(w):
        (List[((Array.T[nat], nat), nat)]);
    (pa, w)
  }

def max_list_aux[A, B : ord](f: A => B, m: B, x2: List[A]): B = (f, m, x2) match
  {
  case (f, m, Nil) => m
  case (f, m, x :: xs) => max_list_aux[A, B](f, max[B](f(x), m), xs)
}

def max_list[A, B : ord](f: A => B, x1: List[A]): B = (f, x1) match {
  case (f, Nil) => sys.error("undefined")
  case (f, x :: xs) => max_list_aux[A, B](f, f(x), xs)
}

def elim_step_code_scoped_ereal_ops_uu_vec_ops_uu_set_ops_api_input_doms_uu_upt_zero_api_input_dims_uu(api_input:
                         api_input_ext[nat, (DiffArray.T[Option[real]], nat),
Unit],
                        iF: (nat, List[(((Array.T[nat], nat)) => ereal, nat)])):
      (nat, List[(((Array.T[nat], nat)) => ereal, nat)])
  =
  {
    val (i, f) = iF: ((nat, List[(((Array.T[nat], nat)) => ereal, nat)]))
    val l =
      nth[nat](upt.apply(zero_nata).apply(api_input_dims[nat,
                  (DiffArray.T[Option[real]], nat), Unit](api_input)),
                i):
        nat
    val (e, ea) =
      partition[(((Array.T[nat], nat)) => ereal,
                  nat)](((sf: (((Array.T[nat], nat)) => ereal, nat)) =>
                          bit_nat((scoped_fn_op_scope[(((Array.T[nat], nat)) =>
                 ereal,
                nat),
               (Array.T[nat], nat), ereal, nat,
               scoped_fn_ereal_ops_ext[(((Array.T[nat], nat)) => ereal, nat),
(Array.T[nat], nat), Unit]](scoped_ereal_ops_uua(api_input))).apply(sf),
                                   l)),
                         f):
        ((List[(((Array.T[nat], nat)) => ereal, nat)],
          List[(((Array.T[nat], nat)) => ereal, nat)]))
    val e_s =
      map[(((Array.T[nat], nat)) => ereal, nat),
           nat](scoped_fn_op_scope[(((Array.T[nat], nat)) => ereal, nat),
                                    (Array.T[nat], nat), ereal, nat,
                                    scoped_fn_ereal_ops_ext[(((Array.T[nat],
                       nat)) =>
                       ereal,
                      nat),
                     (Array.T[nat], nat),
                     Unit]](scoped_ereal_ops_uua(api_input)),
                 e):
        (List[nat])
    val ds =
      upt.apply(zero_nata).apply((api_input_doms[nat,
          (DiffArray.T[Option[real]], nat), Unit](api_input)).apply(l)):
        (List[nat])
    val eb =
      ((x: (Array.T[nat], nat)) =>
        max_list[nat, ereal](((x_l: nat) =>
                               sum_list[ereal](map[(((Array.T[nat], nat)) =>
              ereal,
             nat),
            ereal](((fa: (((Array.T[nat], nat)) => ereal, nat)) =>
                     (scoped_fn_op_alpha[(((Array.T[nat], nat)) => ereal, nat),
  (Array.T[nat], nat), ereal, nat,
  scoped_fn_ereal_ops_ext[(((Array.T[nat], nat)) => ereal, nat),
                           (Array.T[nat], nat),
                           Unit]](scoped_ereal_ops_uua(api_input))).apply(fa).apply((vec_op_update[(Array.T[nat],
                     nat),
                    nat, nat,
                    Unit](vec_ops_uua(api_input))).apply(x).apply(l).apply(x_l))),
                    e))),
                              ds)):
        (((Array.T[nat], nat)) => ereal)
    val scope_e = unset_bit_nat(l, Union_sets_set_ops(e_s)): nat
    val e_fn =
      (scoped_fn_op_eval[(((Array.T[nat], nat)) => ereal, nat),
                          (Array.T[nat], nat), ereal, nat,
                          scoped_fn_ereal_ops_ext[(((Array.T[nat], nat)) =>
             ereal,
            nat),
           (Array.T[nat], nat),
           Unit]](scoped_ereal_ops_uua(api_input))).apply((scoped_fn_op_from_fn[(((Array.T[nat],
   nat)) =>
   ereal,
  nat),
 (Array.T[nat], nat), ereal, nat,
 scoped_fn_ereal_ops_ext[(((Array.T[nat], nat)) => ereal, nat),
                          (Array.T[nat], nat),
                          Unit]](scoped_ereal_ops_uua(api_input))).apply(scope_e).apply(eb)):
        ((((Array.T[nat], nat)) => ereal, nat));
    (plus_nata(i, one_nata), e_fn :: ea)
  }

def elim_aux_code_scoped_ereal_ops_uu_vec_ops_uu_set_ops_api_input_dims_uu_api_input_doms_uu_uu_upt_zero_api_input_dims_uu(api_input:
     api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
    fs: List[(((Array.T[nat], nat)) => ereal, nat)]):
      (nat, List[(((Array.T[nat], nat)) => ereal, nat)])
  =
  (funpow[(nat, List[(((Array.T[nat], nat)) => ereal,
                       nat)])](api_input_dims[nat,
       (DiffArray.T[Option[real]], nat), Unit](api_input),
                                ((a: (nat, List[(((Array.T[nat], nat)) => ereal,
          nat)]))
                                   =>
                                  elim_step_code_scoped_ereal_ops_uu_vec_ops_uu_set_ops_api_input_doms_uu_upt_zero_api_input_dims_uu(api_input,
              a)))).apply((zero_nata, fs))

def elim_max_code_scoped_ereal_ops_uu_vec_ops_uu_set_ops_api_input_dims_uu_api_input_doms_uu_uu_upt_zero_api_input_dims_uu(api_input:
     api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
    fs: List[(((Array.T[nat], nat)) => ereal, nat)]):
      ereal
  =
  sum_list[ereal](map[(((Array.T[nat], nat)) => ereal, nat),
                       ereal](((f: (((Array.T[nat], nat)) => ereal, nat)) =>
                                (scoped_fn_op_alpha[(((Array.T[nat], nat)) =>
               ereal,
              nat),
             (Array.T[nat], nat), ereal, nat,
             scoped_fn_ereal_ops_ext[(((Array.T[nat], nat)) => ereal, nat),
                                      (Array.T[nat], nat),
                                      Unit]](scoped_ereal_ops_uua(api_input))).apply(f).apply(vec_op_empty[(Array.T[nat],
                             nat),
                            nat, nat, Unit](vec_ops_uua(api_input)))),
                               snd[nat, List[(((Array.T[nat], nat)) => ereal,
       nat)]](elim_aux_code_scoped_ereal_ops_uu_vec_ops_uu_set_ops_api_input_dims_uu_api_input_doms_uu_uu_upt_zero_api_input_dims_uu(api_input,
              fs))))

def bellman_diff_code_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_scoped_real_ops_uu_uu_uu_uu(api_input:
                                api_input_ext[nat,
       (DiffArray.T[Option[real]], nat), Unit],
                               g_cache:
                                 nat =>
                                   nat => (((Array.T[nat], nat)) => real, nat),
                               w_code: nat => real, a_code: nat, i: nat):
      (((Array.T[nat], nat)) => real, nat)
  =
  (scoped_fn_real_op_scale[(((Array.T[nat], nat)) => real, nat),
                            (Array.T[nat], nat), nat,
                            Unit](scoped_real_ops_uua(api_input))).apply((scoped_fn_real_op_diff[(((Array.T[nat],
                    nat)) =>
                    real,
                   nat),
                  (Array.T[nat], nat), nat,
                  Unit](scoped_real_ops_uua(api_input))).apply((h_code_scoped_real_ops_uu_vec_ops_uu_uu(api_input)).apply(i)).apply((scoped_fn_real_op_scale[(((Array.T[nat],
nat)) =>
real,
                                       nat),
                                      (Array.T[nat], nat), nat,
                                      Unit](scoped_real_ops_uua(api_input))).apply((g_cache(i))(a_code)).apply(api_input_l_code[nat,
         (DiffArray.T[Option[real]], nat), Unit](api_input)))).apply(w_code(i))

def hg_inst_code_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_scoped_real_ops_uu_uu_uu_uu_uu(api_input:
                              api_input_ext[nat,
     (DiffArray.T[Option[real]], nat), Unit],
                             g_cache:
                               nat =>
                                 nat => (((Array.T[nat], nat)) => real, nat),
                             w_code: nat => real, t_code: (Array.T[nat], nat),
                             a_code: nat, i: nat):
      (((Array.T[nat], nat)) => real, nat)
  =
  (scoped_fn_op_eval[(((Array.T[nat], nat)) => real, nat), (Array.T[nat], nat),
                      real, nat,
                      scoped_fn_real_ops_ext[(((Array.T[nat], nat)) => real,
       nat),
      Unit]](scoped_real_ops_uua(api_input))).apply((scoped_fn_op_inst[(((Array.T[nat],
                                  nat)) =>
                                  real,
                                 nat),
                                (Array.T[nat], nat), real, nat,
                                scoped_fn_real_ops_ext[(((Array.T[nat], nat)) =>
                  real,
                 nat),
                Unit]](scoped_real_ops_uua(api_input))).apply(bellman_diff_code_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_scoped_real_ops_uu_uu_uu_uu(api_input,
         g_cache, w_code, a_code, i)).apply(t_code))

def r_inst_code_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_scoped_real_ops_uu_uu_uua(api_input:
          api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
         t_code: (Array.T[nat], nat), a_code: nat, i: nat):
      (((Array.T[nat], nat)) => real, nat)
  =
  (scoped_fn_op_eval[(((Array.T[nat], nat)) => real, nat), (Array.T[nat], nat),
                      real, nat,
                      scoped_fn_real_ops_ext[(((Array.T[nat], nat)) => real,
       nat),
      Unit]](scoped_real_ops_uua(api_input))).apply((scoped_fn_op_inst[(((Array.T[nat],
                                  nat)) =>
                                  real,
                                 nat),
                                (Array.T[nat], nat), real, nat,
                                scoped_fn_real_ops_ext[(((Array.T[nat], nat)) =>
                  real,
                 nat),
                Unit]](scoped_real_ops_uua(api_input))).apply((rewards_code_scoped_real_ops_uu_vec_ops_uu_uu(api_input)).apply(a_code).apply(i)).apply(t_code))

def epsilon_max_code_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_ereal_ops_uu_scoped_real_ops_uu_vec_ops_uu_set_ops_ste_ops_uu_uu_uu_uu_uu(api_input:
                                 api_input_ext[nat,
        (DiffArray.T[Option[real]], nat), Unit],
                                g_cache:
                                  nat =>
                                    nat => (((Array.T[nat], nat)) => real, nat),
                                w_code: nat => real,
                                ts_code: List[(Array.T[nat], nat)],
                                t_code: (Array.T[nat], nat), a_code: nat):
      ereal
  =
  {
    val c_code =
      map[nat, (((Array.T[nat], nat)) => real,
                 nat)](((a: nat) =>
                         hg_inst_code_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_scoped_real_ops_uu_uu_uu_uu_uu(api_input,
          g_cache, w_code, t_code, a_code, a)),
                        upt.apply(zero_nata).apply(api_input_h_dim_code[nat,
                                 (DiffArray.T[Option[real]], nat),
                                 Unit](api_input))):
        (List[(((Array.T[nat], nat)) => real, nat)])
    val neg_C_code =
      map[(((Array.T[nat], nat)) => real, nat),
           (((Array.T[nat], nat)) => real,
             nat)](((f: (((Array.T[nat], nat)) => real, nat)) =>
                     (scoped_fn_real_op_scale[(((Array.T[nat], nat)) => real,
        nat),
       (Array.T[nat], nat), nat,
       Unit](scoped_real_ops_uua(api_input))).apply(f).apply(uminus_reala(one_reala))),
                    c_code):
        (List[(((Array.T[nat], nat)) => real, nat)])
    val c_codea =
      map[(((Array.T[nat], nat)) => real, nat),
           (((Array.T[nat], nat)) => ereal,
             nat)](((a: (((Array.T[nat], nat)) => real, nat)) =>
                     scoped_to_ereal[(Array.T[nat], nat), nat](a)),
                    c_code):
        (List[(((Array.T[nat], nat)) => ereal, nat)])
    val neg_C_codea =
      map[(((Array.T[nat], nat)) => real, nat),
           (((Array.T[nat], nat)) => ereal,
             nat)](((a: (((Array.T[nat], nat)) => real, nat)) =>
                     scoped_to_ereal[(Array.T[nat], nat), nat](a)),
                    neg_C_code):
        (List[(((Array.T[nat], nat)) => ereal, nat)])
    val b_code =
      map[nat, (((Array.T[nat], nat)) => real,
                 nat)](((a: nat) =>
                         r_inst_code_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_scoped_real_ops_uu_uu_uua(api_input,
                              t_code, a_code, a)),
                        upt.apply(zero_nata).apply(plus_nata((api_input_reward_dim_code[nat,
         (DiffArray.T[Option[real]], nat), Unit](api_input)).apply(a_code),
                      (if (equal_nata(a_code,
                                       api_input_d_code[nat,
                 (DiffArray.T[Option[real]], nat), Unit](api_input)))
                        zero_nata
                        else (api_input_reward_dim_code[nat,
                 (DiffArray.T[Option[real]], nat),
                 Unit](api_input)).apply(api_input_d_code[nat,
                   (DiffArray.T[Option[real]], nat), Unit](api_input)))))):
        (List[(((Array.T[nat], nat)) => real, nat)])
    val neg_b_code =
      map[(((Array.T[nat], nat)) => real, nat),
           (((Array.T[nat], nat)) => real,
             nat)](((f: (((Array.T[nat], nat)) => real, nat)) =>
                     (scoped_fn_real_op_scale[(((Array.T[nat], nat)) => real,
        nat),
       (Array.T[nat], nat), nat,
       Unit](scoped_real_ops_uua(api_input))).apply(f).apply(uminus_reala(one_reala))),
                    b_code):
        (List[(((Array.T[nat], nat)) => real, nat)])
    val i_code =
      map[(Array.T[nat], nat),
           (((Array.T[nat], nat)) => ereal,
             nat)](((t: (Array.T[nat], nat)) =>
                     (scoped_fn_op_eval[(((Array.T[nat], nat)) => ereal, nat),
 (Array.T[nat], nat), ereal, nat,
 scoped_fn_ereal_ops_ext[(((Array.T[nat], nat)) => ereal, nat),
                          (Array.T[nat], nat),
                          Unit]](scoped_ereal_ops_uua(api_input))).apply((scoped_fn_op_inst[(((Array.T[nat],
               nat)) =>
               ereal,
              nat),
             (Array.T[nat], nat), ereal, nat,
             scoped_fn_ereal_ops_ext[(((Array.T[nat], nat)) => ereal, nat),
                                      (Array.T[nat], nat),
                                      Unit]](scoped_ereal_ops_uua(api_input))).apply((scoped_fn_ereal_op_ind[(((Array.T[nat],
                                nat)) =>
                                ereal,
                               nat),
                              (Array.T[nat], nat), nat,
                              Unit](scoped_ereal_ops_uua(api_input))).apply(t)).apply(t_code))),
                    ts_code):
        (List[(((Array.T[nat], nat)) => ereal, nat)])
    val b_codea =
      map[(((Array.T[nat], nat)) => real, nat),
           (((Array.T[nat], nat)) => ereal,
             nat)](((a: (((Array.T[nat], nat)) => real, nat)) =>
                     scoped_to_ereal[(Array.T[nat], nat), nat](a)),
                    b_code) ++
        i_code:
        (List[(((Array.T[nat], nat)) => ereal, nat)])
    val neg_b_codea =
      map[(((Array.T[nat], nat)) => real, nat),
           (((Array.T[nat], nat)) => ereal,
             nat)](((a: (((Array.T[nat], nat)) => real, nat)) =>
                     scoped_to_ereal[(Array.T[nat], nat), nat](a)),
                    neg_b_code) ++
        i_code:
        (List[(((Array.T[nat], nat)) => ereal, nat)])
    val epsilon_pos_code =
      elim_max_code_scoped_ereal_ops_uu_vec_ops_uu_set_ops_api_input_dims_uu_api_input_doms_uu_uu_upt_zero_api_input_dims_uu(api_input,
      c_codea ++ neg_b_codea):
        ereal
    val a =
      elim_max_code_scoped_ereal_ops_uu_vec_ops_uu_set_ops_api_input_dims_uu_api_input_doms_uu_uu_upt_zero_api_input_dims_uu(api_input,
      neg_C_codea ++ b_codea):
        ereal;
    max[ereal](epsilon_pos_code, a)
  }

def error_branch_code_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_real_ops_uu_vec_ops_uu_set_ops_ste_ops_scoped_ereal_ops_uu_uu_uu(api_input:
                         api_input_ext[nat, (DiffArray.T[Option[real]], nat),
Unit],
                        w_code: nat => real,
                        g_cache:
                          nat => nat => (((Array.T[nat], nat)) => real, nat),
                        t: (Array.T[nat], nat), a: nat,
                        ts: List[(Array.T[nat], nat)]):
      ereal
  =
  epsilon_max_code_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_ereal_ops_uu_scoped_real_ops_uu_vec_ops_uu_set_ops_ste_ops_uu_uu_uu_uu_uu(api_input,
                              g_cache, w_code, ts, t, a)

def sup_ereal(x: ereal, y: ereal): ereal = max[ereal](x, y)

def update_err_iter_code_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_real_ops_uu_vec_ops_uu_set_ops_ste_ops_scoped_ereal_ops_uu_uu_uu(api_input:
                            api_input_ext[nat, (DiffArray.T[Option[real]], nat),
   Unit],
                           w_code: nat => real,
                           g_cache:
                             nat =>
                               nat => (((Array.T[nat], nat)) => real, nat)):
      (((Array.T[nat], nat), nat)) =>
        ((List[(Array.T[nat], nat)], ereal)) =>
          (List[(Array.T[nat], nat)], ereal)
  =
  ((a: ((Array.T[nat], nat), nat)) =>
    {
      val (t, aa) = a: (((Array.T[nat], nat), nat));
      ((b: (List[(Array.T[nat], nat)], ereal)) =>
        {
          val (ts, err) = b: ((List[(Array.T[nat], nat)], ereal));
          (t :: ts,
            sup_ereal(error_branch_code_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_real_ops_uu_vec_ops_uu_set_ops_ste_ops_scoped_ereal_ops_uu_uu_uu(api_input,
  w_code, g_cache, t, aa, ts),
                       err))
        })
    })

def err_list_code_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_real_ops_uu_vec_ops_uu_set_ops_ste_ops_scoped_ereal_ops_uu_uu_uu_uu(api_input:
                        api_input_ext[nat, (DiffArray.T[Option[real]], nat),
                                       Unit],
                       w_code: nat => real,
                       g_cache:
                         nat => nat => (((Array.T[nat], nat)) => real, nat),
                       dec_pol_code: List[((Array.T[nat], nat), nat)]):
      ereal
  =
  snd[List[(Array.T[nat], nat)],
       ereal](fold[((Array.T[nat], nat), nat),
                    (List[(Array.T[nat], nat)],
                      ereal)](update_err_iter_code_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_real_ops_uu_vec_ops_uu_set_ops_ste_ops_scoped_ereal_ops_uu_uu_uu(api_input,
             w_code, g_cache),
                               dec_pol_code, (Nil, zero_ereala)))

def factored_bellman_err_code_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_real_ops_uu_vec_ops_uu_set_ops_ste_ops_scoped_ereal_ops_uu_uu_uu_uu(api_input:
                                    api_input_ext[nat,
           (DiffArray.T[Option[real]], nat), Unit],
                                   w_code: nat => real,
                                   g_cache:
                                     nat =>
                                       nat =>
 (((Array.T[nat], nat)) => real, nat),
                                   dec_pol_code:
                                     List[((Array.T[nat], nat), nat)]):
      real
  =
  real_of_ereal(err_list_code_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_real_ops_uu_vec_ops_uu_set_ops_ste_ops_scoped_ereal_ops_uu_uu_uu_uu(api_input,
                                   w_code, g_cache, dec_pol_code))

def bellman_err_code_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_real_ops_uu_vec_ops_uu_set_ops_ste_ops_scoped_ereal_ops_uu(api_input:
                  api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
                 g: nat => nat => (((Array.T[nat], nat)) => real, nat),
                 p: List[((Array.T[nat], nat), nat)], w: nat => real):
      real
  =
  factored_bellman_err_code_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_real_ops_uu_vec_ops_uu_set_ops_ste_ops_scoped_ereal_ops_uu_uu_uu_uu(api_input,
                                 w, g, p)

def api_input_epsilon_code[A, B, C](x0: api_input_ext[A, B, C]): real = x0 match
  {
  case api_input_exta(api_input_dims, api_input_doms, api_input_t_max_code,
                       api_input_epsilon_code, api_input_rewards_code_fn,
                       api_input_rewards_scope_code, api_input_reward_dim_code,
                       api_input_actions_code, api_input_d_code,
                       api_input_transitions_code_fn,
                       api_input_transitions_scopes_code, api_input_l_code,
                       api_input_h_code_fn, api_input_h_scope_code,
                       api_input_h_dim_code, api_input_effects_code, more)
    => api_input_epsilon_code
}

def api_input_t_max_code[A, B, C](x0: api_input_ext[A, B, C]): nat = x0 match {
  case api_input_exta(api_input_dims, api_input_doms, api_input_t_max_code,
                       api_input_epsilon_code, api_input_rewards_code_fn,
                       api_input_rewards_scope_code, api_input_reward_dim_code,
                       api_input_actions_code, api_input_d_code,
                       api_input_transitions_code_fn,
                       api_input_transitions_scopes_code, api_input_l_code,
                       api_input_h_code_fn, api_input_h_scope_code,
                       api_input_h_dim_code, api_input_effects_code, more)
    => api_input_t_max_code
}

def all_interval_nat(p: nat => Boolean, i: nat, j: nat): Boolean =
  less_eq_nat(j, i) || p(i) && all_interval_nat(p, Suc(i), j)

def api_aux_code_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_actions_code_uu_api_input_d_code_uu_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_api_input_effects_code_uu_scoped_real_ops_uu_scoped_pmf_ops_uu_vec_ops_uu_set_ops_ste_ops_constr_map_ops_scoped_ereal_ops_uu_minimize_empty_var_map_ahm_basic_ops_num_vars_var_to_nat_upd_ahm_basic_ops_am_empty_am_update_id_am_invar_am_empty_id_constr_map_ops_am_update_nat_to_var_uu_api_input_t_max_code_uu_api_input_epsilon_code_uu(api_input:
 api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
lp_oracle:
  nat =>
    (List[(nat, real)]) =>
      (List[(nat, List[(nat, real)])]) =>
        (List[(nat, real)]) => Option[LP_Cert[List[(nat, real)]]],
g: nat => nat => (((Array.T[nat], nat)) => real, nat),
pw: (List[((Array.T[nat], nat), nat)], nat => real), t: nat):
      (nat => real,
        (List[((Array.T[nat], nat), nat)],
          (real, (nat, (Boolean, (Boolean, Boolean))))))
  =
  {
    val (p, w) = pw: ((List[((Array.T[nat], nat), nat)], nat => real))
    val (pa, wa) =
      body_code_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_actions_code_uu_api_input_d_code_uu_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_api_input_effects_code_uu_scoped_real_ops_uu_scoped_pmf_ops_uu_vec_ops_uu_set_ops_ste_ops_constr_map_ops_scoped_ereal_ops_uu_minimize_empty_var_map_ahm_basic_ops_num_vars_var_to_nat_upd_ahm_basic_ops_am_empty_am_update_id_am_invar_am_empty_id_constr_map_ops_am_update_nat_to_var_uu(api_input,
                             lp_oracle, g, p):
        ((List[((Array.T[nat], nat), nat)], nat => real))
    val err =
      bellman_err_code_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_scoped_real_ops_uu_vec_ops_uu_set_ops_ste_ops_scoped_ereal_ops_uu(api_input,
                   g, pa, wa):
        real
    val ta = plus_nata(t, one_nata): nat
    val w_eq =
      all_interval_nat(((i: nat) => equal_real(wa(i), w(i))), zero_nata,
                        api_input_h_dim_code[nat,
      (DiffArray.T[Option[real]], nat), Unit](api_input)):
        Boolean
    val err_le =
      less_eq_real(err, api_input_epsilon_code[nat,
        (DiffArray.T[Option[real]], nat), Unit](api_input)):
        Boolean
    val timeout =
      less_eq_nat(api_input_t_max_code[nat, (DiffArray.T[Option[real]], nat),
Unit](api_input),
                   ta):
        Boolean;
    (if (w_eq || (err_le || timeout))
      (wa, (pa, (err, (t, (w_eq, (err_le, timeout))))))
      else api_aux_code_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_actions_code_uu_api_input_d_code_uu_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_api_input_effects_code_uu_scoped_real_ops_uu_scoped_pmf_ops_uu_vec_ops_uu_set_ops_ste_ops_constr_map_ops_scoped_ereal_ops_uu_minimize_empty_var_map_ahm_basic_ops_num_vars_var_to_nat_upd_ahm_basic_ops_am_empty_am_update_id_am_invar_am_empty_id_constr_map_ops_am_update_nat_to_var_uu_api_input_t_max_code_uu_api_input_epsilon_code_uu(api_input,
       lp_oracle, g, (pa, wa), ta))
  }

def pmf_alpha_impl_dflt_ops_iam_basic_ops[A](a: (DiffArray.T[Option[real]], A)):
      pmf[nat]
  =
  sys.error("Code_Inst.pmf_\\<alpha>_impl_dflt_ops_iam_basic_ops")

def iam_rev_iterateoi_aux[A, B](v: nat, a: DiffArray.T[Option[A]],
                                 c: B => Boolean, f: ((nat, A)) => B => B,
                                 sigma: B):
      B
  =
  (if (equal_nata(v, zero_nata)) sigma
    else (if (c(sigma))
           iam_rev_iterateoi_aux[A, B](minus_nata(Suc(minus_nata(v, one_nata)),
           one_nata),
a, c, f,
((array_get[Option[A]](a)).apply(minus_nata(Suc(minus_nata(v, one_nata)),
     one_nata))
   match {
   case None => sigma
   case Some(x) =>
     (f((minus_nata(Suc(minus_nata(v, one_nata)), one_nata), x)))(sigma)
 }))
           else sigma))

def iam_rev_iterateoi[A, B](a: DiffArray.T[Option[A]]):
      (B => Boolean) => (((nat, A)) => B => B) => B => B
  =
  ((b: B => Boolean) => (c: ((nat, A)) => B => B) => (d: B) =>
    iam_rev_iterateoi_aux[A, B](array_length[Option[A]].apply(a), a, b, c, d))

def iteratei_map_op_list_it_dflt_ops_iam_basic_ops[A,
            B](s: DiffArray.T[Option[A]]):
      (B => Boolean) => (((nat, A)) => B => B) => B => B
  =
  iam_rev_iterateoi[A, B](s)

def range_sum_one_dflt_ops_iam_basic_ops(v: DiffArray.T[Option[real]]): Boolean
  =
  equal_real(one_reala,
              (iteratei_map_op_list_it_dflt_ops_iam_basic_ops[real,
                       real](v)).apply(((_: real) =>
 true)).apply(((a: (nat, real)) =>
                {
                  val (_, aa) = a: ((nat, real));
                  ((b: real) => plus_reala(aa, b))
                })).apply(zero_reala))

def iteratei_bmap_op_list_it_iam_basic_ops[A, B](s: DiffArray.T[Option[A]]):
      (B => Boolean) => (((nat, A)) => B => B) => B => B
  =
  iam_rev_iterateoi[A, B](s)

def g_ball_iam_basic_ops[A](m: DiffArray.T[Option[A]],
                             p: ((nat, A)) => Boolean):
      Boolean
  =
  (iteratei_bmap_op_list_it_iam_basic_ops[A,
   Boolean](m)).apply(id[Boolean]).apply(((kv: (nat, A)) => (_: Boolean) =>
   p(kv))).apply(true)

def range_nonneg_dflt_ops_iam_basic_ops(v: DiffArray.T[Option[real]]): Boolean =
  g_ball_iam_basic_ops[real](v, ((a: (nat, real)) =>
                                  {
                                    val (_, aa) = a: ((nat, real));
                                    less_eq_real(zero_reala, aa)
                                  }))

def g_to_list_iam_basic_ops[A](m: DiffArray.T[Option[A]]): List[(nat, A)] =
  (iteratei_bmap_op_list_it_iam_basic_ops[A,
   List[(nat, A)]](m)).apply(((_: List[(nat, A)]) =>
                               true)).apply(((a: (nat, A)) =>
      (b: List[(nat, A)]) => a :: b)).apply(Nil)

def equal_order(x0: ordera, x1: ordera): Boolean = (x0, x1) match {
  case (Lt(), Gt()) => false
  case (Gt(), Lt()) => false
  case (Eq(), Gt()) => false
  case (Gt(), Eq()) => false
  case (Eq(), Lt()) => false
  case (Lt(), Eq()) => false
  case (Gt(), Gt()) => true
  case (Lt(), Lt()) => true
  case (Eq(), Eq()) => true
}

def generator[A, B](x0: generator[A, B]): (B => Boolean, B => (A, B)) = x0 match
  {
  case Generator(x) => x
}

def has_next[A, B](g: generator[A, B]): B => Boolean =
  fst[B => Boolean, B => (A, B)](generator[A, B](g))

def next[A, B](g: generator[A, B]): B => (A, B) =
  snd[B => Boolean, B => (A, B)](generator[A, B](g))

def sorted_list_subset_fusion[A, B,
                               C](less: A => A => Boolean,
                                   eq: A => A => Boolean, g1: generator[A, B],
                                   g2: generator[A, C], s1: B, s2: C):
      Boolean
  =
  (if ((has_next[A, B](g1)).apply(s1))
    {
      val (x, s1a) = (next[A, B](g1)).apply(s1): ((A, B));
      (has_next[A, C](g2)).apply(s2) &&
        {
          val (y, s2a) = (next[A, C](g2)).apply(s2): ((A, C));
          (if ((eq(x))(y))
            sorted_list_subset_fusion[A, B, C](less, eq, g1, g2, s1a, s2a)
            else (less(y))(x) &&
                   sorted_list_subset_fusion[A, B,
      C](less, eq, g1, g2, s1, s2a))
        }
    }
    else true)

def list_all_fusion[A, B](g: generator[A, B], p: A => Boolean, s: B): Boolean =
  (if ((has_next[A, B](g)).apply(s))
    {
      val (x, sa) = (next[A, B](g)).apply(s): ((A, B));
      p(x) && list_all_fusion[A, B](g, p, sa)
    }
    else true)

def rbt_keys_next[A, B](x0: (List[(A, rbta[A, B])], rbta[A, B])):
      (A, (List[(A, rbta[A, B])], rbta[A, B]))
  =
  x0 match {
  case ((k, t) :: kts, Empty()) => (k, (kts, t))
  case (kts, Branch(c, l, k, v, r)) => rbt_keys_next[A, B](((k, r) :: kts, l))
}

def rbt_has_next[A, B, C](x0: (List[(A, rbta[B, C])], rbta[B, C])): Boolean = x0
  match {
  case (Nil, Empty()) => false
  case (vb :: vc, va) => true
  case (v, Branch(vb, vc, vd, ve, vf)) => true
}

def rbt_keys_generator[A, B]: generator[A, (List[(A, rbta[A, B])], rbta[A, B])]
  =
  Generator[(List[(A, rbta[A, B])], rbta[A, B]),
             A]((((a: (List[(A, rbta[A, B])], rbta[A, B])) =>
                   rbt_has_next[A, A, B](a)),
                  ((a: (List[(A, rbta[A, B])], rbta[A, B])) =>
                    rbt_keys_next[A, B](a))))

def lt_of_comp[A](acomp: A => A => ordera, x: A, y: A): Boolean =
  ((acomp(x))(y) match {
     case Eq() => false
     case Lt() => true
     case Gt() => false
   })

def less_eq_set[A : cenum : ceq : ccompare](x0: set[A], c: set[A]): Boolean =
  (x0, c) match {
  case (RBT_set(rbt1), RBT_set(rbt2)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("subset RBT_set RBT_set: ccompare = None");
           (((_: Unit) =>
              less_eq_set[A](RBT_set[A](rbt1), RBT_set[A](rbt2)))).apply(())
           }
       case Some(c) =>
         (ceq[A] match {
            case None =>
              sorted_list_subset_fusion[A,
 (List[(A, rbta[A, Unit])], rbta[A, Unit]),
 (List[(A, rbta[A, Unit])],
   rbta[A, Unit])](((a: A) => (b: A) => lt_of_comp[A](c, a, b)),
                    ((x: A) => (y: A) => equal_order((c(x))(y), Eq())),
                    rbt_keys_generator[A, Unit], rbt_keys_generator[A, Unit],
                    init[A, Unit, A](rbt1), init[A, Unit, A](rbt2))
            case Some(eq) =>
              sorted_list_subset_fusion[A,
 (List[(A, rbta[A, Unit])], rbta[A, Unit]),
 (List[(A, rbta[A, Unit])],
   rbta[A, Unit])](((a: A) => (b: A) => lt_of_comp[A](c, a, b)), eq,
                    rbt_keys_generator[A, Unit], rbt_keys_generator[A, Unit],
                    init[A, Unit, A](rbt1), init[A, Unit, A](rbt2))
          })
     })
  case (Complement(a1), Complement(a2)) => less_eq_set[A](a2, a1)
  case (Collect_set(p), Complement(a)) =>
    less_eq_set[A](a, Collect[A](((x: A) => ! (p(x)))))
  case (Set_Monad(xs), c) => list_all[A](((x: A) => member[A](x, c)), xs)
  case (DList_set(dxs), c) =>
    (ceq[A] match {
       case None =>
         { sys.error("subset DList_set1: ceq = None");
           (((_: Unit) => less_eq_set[A](DList_set[A](dxs), c))).apply(()) }
       case Some(_) => dlist_all[A](((x: A) => member[A](x, c)), dxs)
     })
  case (RBT_set(rbt), b) =>
    (ccompare[A] match {
       case None =>
         { sys.error("subset RBT_set1: ccompare = None");
           (((_: Unit) => less_eq_set[A](RBT_set[A](rbt), b))).apply(()) }
       case Some(_) =>
         list_all_fusion[A, (List[(A, rbta[A, Unit])],
                              rbta[A, Unit])](rbt_keys_generator[A, Unit],
       ((x: A) => member[A](x, b)), init[A, Unit, A](rbt))
     })
}

def list_all2_fusion[A, B, C,
                      D](p: A => B => Boolean, g1: generator[A, C],
                          g2: generator[B, D], s1: C, s2: D):
      Boolean
  =
  (if ((has_next[A, C](g1)).apply(s1))
    (has_next[B, D](g2)).apply(s2) &&
      {
        val (x, s1a) = (next[A, C](g1)).apply(s1): ((A, C))
        val (y, s2a) = (next[B, D](g2)).apply(s2): ((B, D));
        (p(x))(y) && list_all2_fusion[A, B, C, D](p, g1, g2, s1a, s2a)
      }
    else ! (has_next[B, D](g2)).apply(s2))

def set_eq[A : cenum : ceq : ccompare](a: set[A], b: set[A]): Boolean = (a, b)
  match {
  case (RBT_set(rbt1), RBT_set(rbt2)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("set_eq RBT_set RBT_set: ccompare = None");
           (((_: Unit) =>
              set_eq[A](RBT_set[A](rbt1), RBT_set[A](rbt2)))).apply(())
           }
       case Some(c) =>
         (ceq[A] match {
            case None =>
              list_all2_fusion[A, A, (List[(A, rbta[A, Unit])], rbta[A, Unit]),
                                (List[(A, rbta[A, Unit])],
                                  rbta[A,
Unit])](((x: A) => (y: A) => equal_order((c(x))(y), Eq())),
         rbt_keys_generator[A, Unit], rbt_keys_generator[A, Unit],
         init[A, Unit, A](rbt1), init[A, Unit, A](rbt2))
            case Some(eq) =>
              list_all2_fusion[A, A, (List[(A, rbta[A, Unit])], rbta[A, Unit]),
                                (List[(A, rbta[A, Unit])],
                                  rbta[A,
Unit])](eq, rbt_keys_generator[A, Unit], rbt_keys_generator[A, Unit],
         init[A, Unit, A](rbt1), init[A, Unit, A](rbt2))
          })
     })
  case (Complement(a), Complement(b)) => set_eq[A](a, b)
  case (a, b) => less_eq_set[A](a, b) && less_eq_set[A](b, a)
}

def pmf_invar_dflt_ops_iam_basic_ops_bs_ops(v: DiffArray.T[Option[real]],
     s: nat):
      Boolean
  =
  range_nonneg_dflt_ops_iam_basic_ops(v) &&
    (range_sum_one_dflt_ops_iam_basic_ops(v) &&
      (true &&
        (true &&
          set_eq[nat](set[nat](map[(nat, real),
                                    nat](((a: (nat, real)) =>
   fst[nat, real](a)),
  g_to_list_iam_basic_ops[real](v))),
                       set[nat](g_to_list_bs_basic_ops(s))))))

def array_get_oo[A](x: A, a: DiffArray.T[A]): nat => A =
  comp[BigInt, A,
        nat](((b: BigInt) => DiffArray.get_oo(x,a,b.toInt)),
              ((aa: nat) => integer_of_nat(aa)))

def iam_alpha[A](a: DiffArray.T[Option[A]], i: nat): Option[A] =
  (array_get_oo[Option[A]](None, a)).apply(i)

def pmf_lookup_dflt_ops_iam_basic_ops(v: DiffArray.T[Option[real]], i: nat):
      real
  =
  (iam_alpha[real](v, i) match {
     case None => zero_reala
     case Some(p) => p
   })

def pmf_ops_dflt_ops_iam_basic_ops_bs_ops:
      pmf_ops_ext[(DiffArray.T[Option[real]], nat), nat, nat, Unit]
  =
  pmf_ops_exta[(DiffArray.T[Option[real]], nat), nat, nat,
                Unit](((a: (DiffArray.T[Option[real]], nat)) =>
                        pmf_alpha_impl_dflt_ops_iam_basic_ops[nat](a)),
                       ((a: (DiffArray.T[Option[real]], nat)) =>
                         {
                           val (v, _) = a: ((DiffArray.T[Option[real]], nat));
                           ((aa: nat) =>
                             pmf_lookup_dflt_ops_iam_basic_ops(v, aa))
                         }),
                       ((a: (DiffArray.T[Option[real]], nat)) =>
                         snd[DiffArray.T[Option[real]], nat](a)),
                       ((a: (DiffArray.T[Option[real]], nat)) =>
                         {
                           val (aa, b) = a: ((DiffArray.T[Option[real]], nat));
                           pmf_invar_dflt_ops_iam_basic_ops_bs_ops(aa, b)
                         }),
                       ())

def prod_list[A : monoid_mult](xs: List[A]): A =
  (foldr[A, A](((a: A) => (b: A) => times[A](a, b)), xs)).apply(one[A])

def pmf_op_prob_at[A, B, C, D](x0: pmf_ops_ext[A, B, C, D]): A => B => real = x0
  match {
  case pmf_ops_exta(pmf_alpha, pmf_op_prob_at, pmf_op_supp, pmf_op_invar, more)
    => pmf_op_prob_at
}

def g_elem_scoped_real_ops_uu_scoped_pmf_ops_uu_vec_ops_uu_set_ops_pmf_ops_dflt_ops_iam_basic_ops_bs_ops_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu[A](api_input:
       api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
      h: (((Array.T[nat], nat)) => real, nat), hs: nat,
      h_ys: List[(Array.T[nat], nat)], i: A, a: nat, x: (Array.T[nat], nat)):
      real
  =
  {
    val ts =
      (transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu(api_input)).apply(a):
        (nat =>
          (((Array.T[nat], nat)) => (DiffArray.T[Option[real]], nat), nat));
    sum_list[real](map[(Array.T[nat], nat),
                        real](((y: (Array.T[nat], nat)) =>
                                times_reala(prod_list[real](map[nat,
                         real](((ia: nat) =>
                                 (pmf_op_prob_at[(DiffArray.T[Option[real]],
           nat),
          nat, nat,
          Unit](pmf_ops_dflt_ops_iam_basic_ops_bs_ops)).apply((scoped_fn_op_alpha[(((Array.T[nat],
     nat)) =>
     (DiffArray.T[Option[real]], nat),
    nat),
   (Array.T[nat], nat), (DiffArray.T[Option[real]], nat), nat,
   Unit](scoped_pmf_ops_uua(api_input))).apply(ts(ia)).apply(x)).apply((vec_op_idx[(Array.T[nat],
     nat),
    nat, nat, Unit](vec_ops_uua(api_input))).apply(y).apply(ia))),
                                g_to_list_bs_basic_ops(hs))),
     (scoped_fn_op_alpha[(((Array.T[nat], nat)) => real, nat),
                          (Array.T[nat], nat), real, nat,
                          scoped_fn_real_ops_ext[(((Array.T[nat], nat)) => real,
           nat),
          Unit]](scoped_real_ops_uua(api_input))).apply(h).apply(y))),
                               h_ys))
  }

def g_code_i_a_scoped_real_ops_uu_scoped_pmf_ops_uu_vec_ops_uu_set_ops_pmf_ops_dflt_ops_iam_basic_ops_bs_ops_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu[A](api_input:
           api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
          h: (((Array.T[nat], nat)) => real, nat), hs: nat,
          h_ys: List[(Array.T[nat], nat)], i: A, a: nat):
      (((Array.T[nat], nat)) => real, nat)
  =
  {
    val parents =
      Gamma_a_code_scoped_pmf_ops_uu_set_ops_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu(api_input,
                       a, hs):
        nat
    val gi =
      ((b: (Array.T[nat], nat)) =>
        g_elem_scoped_real_ops_uu_scoped_pmf_ops_uu_vec_ops_uu_set_ops_pmf_ops_dflt_ops_iam_basic_ops_bs_ops_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu[A](api_input,
          h, hs, h_ys, i, a, b)):
        (((Array.T[nat], nat)) => real);
    (scoped_fn_op_eval[(((Array.T[nat], nat)) => real, nat),
                        (Array.T[nat], nat), real, nat,
                        scoped_fn_real_ops_ext[(((Array.T[nat], nat)) => real,
         nat),
        Unit]](scoped_real_ops_uua(api_input))).apply((scoped_fn_op_from_fn[(((Array.T[nat],
                                       nat)) =>
                                       real,
                                      nat),
                                     (Array.T[nat], nat), real, nat,
                                     scoped_fn_real_ops_ext[(((Array.T[nat],
                       nat)) =>
                       real,
                      nat),
                     Unit]](scoped_real_ops_uua(api_input))).apply(parents).apply(gi))
  }

def g_code_i_scoped_real_ops_uu_scoped_pmf_ops_uu_vec_ops_uu_set_ops_pmf_ops_dflt_ops_iam_basic_ops_bs_ops_api_input_doms_uu_api_input_actions_code_uu_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu(api_input:
          api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
         i: nat):
      nat => (((Array.T[nat], nat)) => real, nat)
  =
  {
    val h =
      (h_code_scoped_real_ops_uu_vec_ops_uu_uu(api_input)).apply(i):
        ((((Array.T[nat], nat)) => real, nat))
    val hs =
      (scoped_fn_op_scope[(((Array.T[nat], nat)) => real, nat),
                           (Array.T[nat], nat), real, nat,
                           scoped_fn_real_ops_ext[(((Array.T[nat], nat)) =>
             real,
            nat),
           Unit]](scoped_real_ops_uua(api_input))).apply(h):
        nat
    val h_ys =
      assignments_impl_vec_ops_uu_set_ops_api_input_doms_uu(api_input, hs):
        (List[(Array.T[nat], nat)])
    val as =
      upt.apply(zero_nata).apply(api_input_actions_code[nat,
                 (DiffArray.T[Option[real]], nat), Unit](api_input)):
        (List[nat])
    val gi =
      ((a: nat) =>
        g_code_i_a_scoped_real_ops_uu_scoped_pmf_ops_uu_vec_ops_uu_set_ops_pmf_ops_dflt_ops_iam_basic_ops_bs_ops_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu[nat](api_input,
                h, hs, h_ys, i, a)):
        (nat => (((Array.T[nat], nat)) => real, nat))
    val a =
      Array.init_list[(((Array.T[nat], nat)) => real,
                        nat)](map[nat, (((Array.T[nat], nat)) => real,
 nat)](gi, as)):
        (Array.T[((((Array.T[nat], nat)) => real, nat))]);
    ((b: nat) => sub[(((Array.T[nat], nat)) => real, nat)](a, b))
  }

def g_arr_scoped_real_ops_uu_scoped_pmf_ops_uu_vec_ops_uu_set_ops_pmf_ops_dflt_ops_iam_basic_ops_bs_ops_api_input_doms_uu_api_input_actions_code_uu_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu(api_input:
                               api_input_ext[nat,
      (DiffArray.T[Option[real]], nat), Unit]):
      Array.T[(nat => (((Array.T[nat], nat)) => real, nat))]
  =
  {
    val is =
      upt.apply(zero_nata).apply(api_input_h_dim_code[nat,
               (DiffArray.T[Option[real]], nat), Unit](api_input)):
        (List[nat])
    val arr =
      Array.init_list[nat =>
                        (((Array.T[nat], nat)) => real,
                          nat)](map[nat, nat =>
   (((Array.T[nat], nat)) => real,
     nat)](((a: nat) =>
             g_code_i_scoped_real_ops_uu_scoped_pmf_ops_uu_vec_ops_uu_set_ops_pmf_ops_dflt_ops_iam_basic_ops_bs_ops_api_input_doms_uu_api_input_actions_code_uu_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu(api_input,
                  a)),
            is)):
        (Array.T[(nat => (((Array.T[nat], nat)) => real, nat))]);
    arr
  }

def api_code_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_actions_code_uu_api_input_d_code_uu_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_api_input_effects_code_uu_scoped_real_ops_uu_scoped_pmf_ops_uu_vec_ops_uu_set_ops_pmf_ops_dflt_ops_iam_basic_ops_bs_ops_ste_ops_constr_map_ops_scoped_ereal_ops_uu_minimize_empty_var_map_ahm_basic_ops_num_vars_var_to_nat_upd_ahm_basic_ops_am_empty_am_update_id_am_invar_am_empty_id_constr_map_ops_am_update_nat_to_var_uu_api_input_t_max_code_uu_api_input_epsilon_code_uu(api_input:
                                   api_input_ext[nat,
          (DiffArray.T[Option[real]], nat), Unit],
                                  lp_oracle:
                                    nat =>
                                      (List[(nat, real)]) =>
(List[(nat, List[(nat, real)])]) =>
  (List[(nat, real)]) => Option[LP_Cert[List[(nat, real)]]]):
      (nat => real,
        (List[((Array.T[nat], nat), nat)],
          (real, (nat, (Boolean, (Boolean, Boolean))))))
  =
  {
    val ga =
      g_arr_scoped_real_ops_uu_scoped_pmf_ops_uu_vec_ops_uu_set_ops_pmf_ops_dflt_ops_iam_basic_ops_bs_ops_api_input_doms_uu_api_input_actions_code_uu_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu(api_input):
        (Array.T[(nat => (((Array.T[nat], nat)) => real, nat))])
    val gc =
      ((a: nat) => sub[nat => (((Array.T[nat], nat)) => real, nat)](ga, a)):
        (nat => nat => (((Array.T[nat], nat)) => real, nat))
    val w0 = ((_: nat) => zero_reala): (nat => real)
    val p0 =
      (update_dec_list_code_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_actions_code_uu_api_input_d_code_uu_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_api_input_effects_code_uu_scoped_real_ops_uu_scoped_pmf_ops_uu_vec_ops_uu_set_ops(api_input)).apply(gc).apply(w0):
        (List[((Array.T[nat], nat), nat)])
    val res =
      api_aux_code_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_actions_code_uu_api_input_d_code_uu_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_api_input_effects_code_uu_scoped_real_ops_uu_scoped_pmf_ops_uu_vec_ops_uu_set_ops_ste_ops_constr_map_ops_scoped_ereal_ops_uu_minimize_empty_var_map_ahm_basic_ops_num_vars_var_to_nat_upd_ahm_basic_ops_am_empty_am_update_id_am_invar_am_empty_id_constr_map_ops_am_update_nat_to_var_uu_api_input_t_max_code_uu_api_input_epsilon_code_uu(api_input,
  lp_oracle, gc, (p0, w0), zero_nata):
        ((nat => real,
          (List[((Array.T[nat], nat), nat)],
            (real, (nat, (Boolean, (Boolean, Boolean)))))));
    res
  }

def api_code_vec_ops_uu_set_ops_pmf_ops_dflt_ops_iam_basic_ops_bs_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_actions_code_uu_api_input_d_code_uu_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_api_input_effects_code_uu_constr_map_ops_ste_ops_scoped_real_ops_uu_scoped_pmf_ops_uu_scoped_ereal_ops_uu_api_input_t_max_code_uu_api_input_epsilon_code_uu_uu(api_input:
 api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
lp_oracle:
  nat =>
    (List[(nat, real)]) =>
      (List[(nat, List[(nat, real)])]) =>
        (List[(nat, real)]) => Option[LP_Cert[List[(nat, real)]]]):
      (nat => real,
        (List[((Array.T[nat], nat), nat)],
          (real, (nat, (Boolean, (Boolean, Boolean))))))
  =
  api_code_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_actions_code_uu_api_input_d_code_uu_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_api_input_effects_code_uu_scoped_real_ops_uu_scoped_pmf_ops_uu_vec_ops_uu_set_ops_pmf_ops_dflt_ops_iam_basic_ops_bs_ops_ste_ops_constr_map_ops_scoped_ereal_ops_uu_minimize_empty_var_map_ahm_basic_ops_num_vars_var_to_nat_upd_ahm_basic_ops_am_empty_am_update_id_am_invar_am_empty_id_constr_map_ops_am_update_nat_to_var_uu_api_input_t_max_code_uu_api_input_epsilon_code_uu(api_input,
                                lp_oracle)

def scoped_fold_left[A, B](x0: Scoped_Tree[A], f: B => A => B, acc: B): B =
  (x0, f, acc) match {
  case (Scoped_Leaf(x), f, acc) => (f(acc))(x)
  case (Scoped_Node(i, arr), f, acc) =>
    foldl[B, Scoped_Tree[A]](((acca: B) => (st: Scoped_Tree[A]) =>
                               scoped_fold_left[A, B](st, f, acca)),
                              acc, list_of[Scoped_Tree[A]](arr))
}

def scoped_fold_all[A](st: Scoped_Tree[A], p: A => Boolean): Boolean =
  scoped_fold_left[A, Boolean](st, ((acc: Boolean) => (y: A) => acc && p(y)),
                                true)

def pmf_op_invar[A, B, C, D](x0: pmf_ops_ext[A, B, C, D]): A => Boolean = x0
  match {
  case pmf_ops_exta(pmf_alpha, pmf_op_prob_at, pmf_op_supp, pmf_op_invar, more)
    => pmf_op_invar
}

def pmf_op_supp[A, B, C, D](x0: pmf_ops_ext[A, B, C, D]): A => C = x0 match {
  case pmf_ops_exta(pmf_alpha, pmf_op_prob_at, pmf_op_supp, pmf_op_invar, more)
    => pmf_op_supp
}

def valid_pmfs_pmf_ops_dflt_ops_iam_basic_ops_bs_ops_set_ops_uu(api_input:
                          api_input_ext[nat, (DiffArray.T[Option[real]], nat),
 Unit],
                         f: Scoped_Tree[(DiffArray.T[Option[real]], nat)],
                         i: nat):
      Boolean
  =
  scoped_fold_all[(DiffArray.T[Option[real]],
                    nat)](f, ((pmf: (DiffArray.T[Option[real]], nat)) =>
                               (pmf_op_invar[(DiffArray.T[Option[real]], nat),
      nat, nat, Unit](pmf_ops_dflt_ops_iam_basic_ops_bs_ops)).apply(pmf) &&
                                 g_ball_bs_basic_ops((pmf_op_supp[(DiffArray.T[Option[real]],
                            nat),
                           nat, nat,
                           Unit](pmf_ops_dflt_ops_iam_basic_ops_bs_ops)).apply(pmf),
              ((y: nat) =>
                less_nat(y, (api_input_doms[nat,
     (DiffArray.T[Option[real]], nat), Unit](api_input)).apply(i))))))

def scoped_tree_scopes_set_ops[A](x0: Scoped_Tree[A], s: nat): Boolean = (x0, s)
  match {
  case (Scoped_Leaf(x), s) => true
  case (Scoped_Node(i, arr), s) =>
    bit_nat(s, i) &&
      list_all[Scoped_Tree[A]](((a: Scoped_Tree[A]) =>
                                 scoped_tree_scopes_set_ops[A](a, s)),
                                list_of[Scoped_Tree[A]](arr))
}

def scoped_tree_lengths_uu[A](api_input:
                                api_input_ext[nat,
       (DiffArray.T[Option[real]], nat), Unit],
                               x1: Scoped_Tree[A]):
      Boolean
  =
  (api_input, x1) match {
  case (api_input, Scoped_Node(i, arr)) =>
    equal_nata(length[Scoped_Tree[A]](arr),
                (api_input_doms[nat, (DiffArray.T[Option[real]], nat),
                                 Unit](api_input)).apply(i)) &&
      list_all[Scoped_Tree[A]](((a: Scoped_Tree[A]) =>
                                 scoped_tree_lengths_uu[A](api_input, a)),
                                list_of[Scoped_Tree[A]](arr))
  case (api_input, Scoped_Leaf(x)) => true
}

def check_scoped_tree_set_ops_uu[A](api_input:
                                      api_input_ext[nat,
             (DiffArray.T[Option[real]], nat), Unit],
                                     f: Scoped_Tree[A], s: nat):
      Boolean
  =
  scoped_tree_lengths_uu[A](api_input, f) && scoped_tree_scopes_set_ops[A](f, s)

def check_scope_fn_set_ops_api_input_dims_uu_uu[A](api_input:
             api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
            f: Scoped_Tree[A], s: nat):
      Boolean
  =
  true &&
    (g_ball_bs_basic_ops(s, ((i: nat) =>
                              less_nat(i,
api_input_dims[nat, (DiffArray.T[Option[real]], nat), Unit](api_input)))) &&
      check_scoped_tree_set_ops_uu[A](api_input, f, s))

def transitions_code_valid_set_ops_pmf_ops_dflt_ops_iam_basic_ops_bs_ops_set_ops_api_input_dims_uu_uu(api_input:
                        api_input_ext[nat, (DiffArray.T[Option[real]], nat),
                                       Unit]):
      Boolean
  =
  all_interval_nat(((a: nat) =>
                     all_interval_nat(((i: nat) =>
{
  val act =
    (if (bit_nat((api_input_effects_code[nat, (DiffArray.T[Option[real]], nat),
  Unit](api_input)).apply(a),
                  i))
      a else api_input_d_code[nat, (DiffArray.T[Option[real]], nat),
                               Unit](api_input)):
      nat;
  check_scope_fn_set_ops_api_input_dims_uu_uu[(DiffArray.T[Option[real]],
        nat)](api_input,
               (api_input_transitions_code_fn[nat,
       (DiffArray.T[Option[real]], nat), Unit](api_input)).apply(act).apply(i),
               (api_input_transitions_scopes_code[nat,
           (DiffArray.T[Option[real]], nat),
           Unit](api_input)).apply(act).apply(i)) &&
    valid_pmfs_pmf_ops_dflt_ops_iam_basic_ops_bs_ops_set_ops_uu(api_input,
                         (api_input_transitions_code_fn[nat,
                 (DiffArray.T[Option[real]], nat),
                 Unit](api_input)).apply(act).apply(i),
                         i)
}),
                                       zero_nata,
                                       api_input_dims[nat,
               (DiffArray.T[Option[real]], nat), Unit](api_input))),
                    zero_nata,
                    api_input_actions_code[nat,
    (DiffArray.T[Option[real]], nat), Unit](api_input))

def reward_code_valid_set_ops_api_input_dims_uu_uu(api_input:
             api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit]):
      Boolean
  =
  all_interval_nat(((a: nat) =>
                     all_interval_nat(((i: nat) =>
check_scope_fn_set_ops_api_input_dims_uu_uu[real](api_input,
           (api_input_rewards_code_fn[nat, (DiffArray.T[Option[real]], nat),
                                       Unit](api_input)).apply(a).apply(i),
           (api_input_rewards_scope_code[nat, (DiffArray.T[Option[real]], nat),
  Unit](api_input)).apply(a).apply(i))),
                                       zero_nata,
                                       (api_input_reward_dim_code[nat,
                           (DiffArray.T[Option[real]], nat),
                           Unit](api_input)).apply(a))),
                    zero_nata,
                    api_input_actions_code[nat,
    (DiffArray.T[Option[real]], nat), Unit](api_input))

def g_isEmpty_bs_basic_ops(s: nat): Boolean =
  (iteratei_bset_op_list_it_bs_basic_ops[Boolean](s)).apply(((c: Boolean) =>
                      c)).apply(((_: nat) => (_: Boolean) => false)).apply(true)

def effects_valid_set_ops_api_input_dims_uu_uu(api_input:
         api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit]):
      Boolean
  =
  less_nat(api_input_d_code[nat, (DiffArray.T[Option[real]], nat),
                             Unit](api_input),
            api_input_actions_code[nat, (DiffArray.T[Option[real]], nat),
                                    Unit](api_input)) &&
    (all_interval_nat(((a: nat) =>
                        true &&
                          g_ball_bs_basic_ops((api_input_effects_code[nat,
                               (DiffArray.T[Option[real]], nat),
                               Unit](api_input)).apply(a),
       ((i: nat) =>
         less_nat(i, api_input_dims[nat, (DiffArray.T[Option[real]], nat),
                                     Unit](api_input))))),
                       zero_nata,
                       api_input_actions_code[nat,
       (DiffArray.T[Option[real]], nat), Unit](api_input)) &&
      g_isEmpty_bs_basic_ops((api_input_effects_code[nat,
              (DiffArray.T[Option[real]], nat),
              Unit](api_input)).apply(api_input_d_code[nat,
                (DiffArray.T[Option[real]], nat), Unit](api_input))))

def h_code_valid_set_ops_api_input_dims_uu_uu(api_input:
        api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit]):
      Boolean
  =
  all_interval_nat(((i: nat) =>
                     check_scope_fn_set_ops_api_input_dims_uu_uu[real](api_input,
                                (api_input_h_code_fn[nat,
              (DiffArray.T[Option[real]], nat), Unit](api_input)).apply(i),
                                (api_input_h_scope_code[nat,
                 (DiffArray.T[Option[real]], nat), Unit](api_input)).apply(i))),
                    zero_nata,
                    api_input_h_dim_code[nat, (DiffArray.T[Option[real]], nat),
  Unit](api_input))

def bot_set[A : ceq : ccompare : set_impl]: set[A] =
  set_empty[A](of_phantom[A, set_impla](set_impl[A]))

def zero_set[A : ceq : ccompare : zero : set_impl]: set[A] =
  insert[A](zero[A], bot_set[A])

def less_set[A : cenum : ceq : ccompare](a: set[A], b: set[A]): Boolean =
  less_eq_set[A](a, b) && ! (less_eq_set[A](b, a))

def doms_valid_api_input_dims_uu_uu(api_input:
                                      api_input_ext[nat,
             (DiffArray.T[Option[real]], nat), Unit]):
      Boolean
  =
  all_interval_nat(((i: nat) =>
                     less_set[nat](zero_set[nat],
                                    set[nat](upt.apply(zero_nata).apply((api_input_doms[nat,
         (DiffArray.T[Option[real]], nat), Unit](api_input)).apply(i))))),
                    zero_nata,
                    api_input_dims[nat, (DiffArray.T[Option[real]], nat),
                                    Unit](api_input))

def dims_valid_api_input_dims_uua(api_input:
                                    api_input_ext[nat,
           (DiffArray.T[Option[real]], nat), Unit]):
      Boolean
  =
  less_nat(zero_nata,
            api_input_dims[nat, (DiffArray.T[Option[real]], nat),
                            Unit](api_input))

def epsilon_code_valid_uu(api_input:
                            api_input_ext[nat, (DiffArray.T[Option[real]], nat),
   Unit]):
      Boolean
  =
  less_real(zero_reala,
             api_input_epsilon_code[nat, (DiffArray.T[Option[real]], nat),
                                     Unit](api_input))

def l_valid_uu(api_input:
                 api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit]):
      Boolean
  =
  less_eq_real(zero_reala,
                api_input_l_code[nat, (DiffArray.T[Option[real]], nat),
                                  Unit](api_input)) &&
    less_real(api_input_l_code[nat, (DiffArray.T[Option[real]], nat),
                                Unit](api_input),
               one_reala)

def input_valid_set_ops_pmf_ops_dflt_ops_iam_basic_ops_bs_ops_set_ops_api_input_dims_uu_uu_uu(api_input:
                api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit]):
      Boolean
  =
  l_valid_uu(api_input) &&
    (epsilon_code_valid_uu(api_input) &&
      (dims_valid_api_input_dims_uua(api_input) &&
        (doms_valid_api_input_dims_uu_uu(api_input) &&
          (effects_valid_set_ops_api_input_dims_uu_uu(api_input) &&
            (h_code_valid_set_ops_api_input_dims_uu_uu(api_input) &&
              (reward_code_valid_set_ops_api_input_dims_uu_uu(api_input) &&
                transitions_code_valid_set_ops_pmf_ops_dflt_ops_iam_basic_ops_bs_ops_set_ops_api_input_dims_uu_uu(api_input)))))))

def solver_checked_scoped_real_ops_uu_ste_ops_scoped_ereal_ops_uu_scoped_pmf_ops_uu_constr_map_ops_vec_ops_uu_set_ops_pmf_ops_dflt_ops_iam_basic_ops_bs_ops_set_ops_api_input_dims_uu_uu_uu_uu(api_input:
                                 api_input_ext[nat,
        (DiffArray.T[Option[real]], nat), Unit],
                                lp_oracle:
                                  nat =>
                                    (List[(nat, real)]) =>
                                      (List[(nat, List[(nat, real)])]) =>
(List[(nat, real)]) => Option[LP_Cert[List[(nat, real)]]]):
      Option[(nat => real,
               (List[((Array.T[nat], nat), nat)],
                 (real, (nat, (Boolean, (Boolean, Boolean))))))]
  =
  (if (input_valid_set_ops_pmf_ops_dflt_ops_iam_basic_ops_bs_ops_set_ops_api_input_dims_uu_uu_uu(api_input))
    Some[(nat => real,
           (List[((Array.T[nat], nat), nat)],
             (real,
               (nat, (Boolean,
                       (Boolean,
                         Boolean))))))](api_code_vec_ops_uu_set_ops_pmf_ops_dflt_ops_iam_basic_ops_bs_ops_api_input_dims_uu_api_input_dims_uu_api_input_doms_uu_rewards_code_scoped_real_ops_uu_vec_ops_uu_uu_uu_api_input_actions_code_uu_api_input_d_code_uu_transitions_code_scoped_pmf_ops_uu_vec_ops_uu_set_ops_uu_api_input_l_code_uu_h_code_scoped_real_ops_uu_vec_ops_uu_uu_api_input_h_dim_code_uu_api_input_effects_code_uu_constr_map_ops_ste_ops_scoped_real_ops_uu_scoped_pmf_ops_uu_scoped_ereal_ops_uu_api_input_t_max_code_uu_api_input_epsilon_code_uu_uu(api_input,
                                    lp_oracle))
    else None)

def solver:
      (api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit]) =>
        (nat =>
          (List[(nat, real)]) =>
            (List[(nat, List[(nat, real)])]) =>
              (List[(nat, real)]) => Option[LP_Cert[List[(nat, real)]]]) =>
          Option[(nat => real,
                   (List[((Array.T[nat], nat), nat)],
                     (real, (nat, (Boolean, (Boolean, Boolean))))))]
  =
  ((a: api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit]) =>
    (b: nat =>
          (List[(nat, real)]) =>
            (List[(nat, List[(nat, real)])]) =>
              (List[(nat, real)]) => Option[LP_Cert[List[(nat, real)]]])
      =>
    solver_checked_scoped_real_ops_uu_ste_ops_scoped_ereal_ops_uu_scoped_pmf_ops_uu_constr_map_ops_vec_ops_uu_set_ops_pmf_ops_dflt_ops_iam_basic_ops_bs_ops_set_ops_api_input_dims_uu_uu_uu_uu(a,
                                b))

def show_err[A : show](e: A): List[char] =
  List(Char(true, false, true, false, false, false, true, false),
        Char(false, true, false, false, true, true, true, false),
        Char(false, true, false, false, true, true, true, false),
        Char(true, true, true, true, false, true, true, false),
        Char(false, true, false, false, true, true, true, false),
        Char(false, true, false, true, true, true, false, false),
        Char(false, false, false, false, false, true, false, false)) ++
    (shows_prec[A](zero_nata, e, Nil) ++ endl)

def show_mat[A, B, C, D](m: tree[((A, tree[(B, C)]), D)]): List[(A, List[B])] =
  map[(A, tree[(B, C)]),
       (A, List[B])](((a: (A, tree[(B, C)])) =>
                       {
                         val (i, v) = a: ((A, tree[(B, C)]));
                         (i, inorder[B, C](v))
                       }),
                      inorder[(A, tree[(B, C)]), D](m))

def show_nata(n: nat): String =
  implode(shows_prec_nat.apply(zero_nata).apply(n).apply(Nil))

def vec_to_list_vec_ops_set_ops_api_input_dims_uu_api_input_doms_uu_api_input_dims_uu(api_input:
        api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
       v: (Array.T[nat], nat)):
      List[Option[nat]]
  =
  map[nat, Option[nat]]((vec_op_alpha[(Array.T[nat], nat), nat, nat,
                                       Unit](vec_ops_set_ops_api_input_dims_uu_api_input_doms_uu(api_input))).apply(v),
                         upt.apply(zero_nata).apply(api_input_dims[nat,
                            (DiffArray.T[Option[real]], nat), Unit](api_input)))

def show_state(solver_input:
                 api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
                s: (Array.T[nat], nat)):
      List[char]
  =
  maps[Option[nat],
        char](((a: Option[nat]) =>
                (a match {
                   case None =>
                     List(Char(true, true, true, true, true, false, true,
                                false))
                   case Some(i) =>
                     shows_prec_nat.apply(zero_nata).apply(i).apply(Nil)
                 })),
               vec_to_list_vec_ops_set_ops_api_input_dims_uu_api_input_doms_uu_api_input_dims_uu(solver_input,
                  s))

def show_pol[A : show](solver_input:
                         api_input_ext[nat, (DiffArray.T[Option[real]], nat),
Unit],
                        p: List[((Array.T[nat], nat), A)]):
      List[char]
  =
  List(Char(false, false, false, false, true, false, true, false),
        Char(true, true, true, true, false, true, true, false),
        Char(false, false, true, true, false, true, true, false),
        Char(true, false, false, true, false, true, true, false),
        Char(true, true, false, false, false, true, true, false),
        Char(true, false, false, true, true, true, true, false),
        Char(false, true, false, true, true, true, false, false)) ++
    (endl ++
      maps[((Array.T[nat], nat), A),
            char](((a: ((Array.T[nat], nat), A)) =>
                    {
                      val (s, aa) = a: (((Array.T[nat], nat), A));
                      List(Char(false, false, false, false, false, true, false,
                                 false),
                            Char(false, false, false, false, false, true, false,
                                  false)) ++
                        (show_state(solver_input, s) ++
                          (List(Char(false, false, false, false, false, true,
                                      false, false),
                                 Char(true, false, true, true, false, true,
                                       false, false),
                                 Char(false, true, true, true, true, true,
                                       false, false),
                                 Char(false, false, false, false, false, true,
                                       false, false)) ++
                            (shows_prec[A](zero_nata, aa, Nil) ++ endl)))
                    }),
                   p))

def show_rat(n: rat): String =
  implode(shows_prec_rat.apply(zero_nata).apply(n).apply(Nil))

def show_weights[A, B, C,
                  D : show](solver_input: api_input_ext[A, B, C], w: nat => D):
      List[char]
  =
  List(Char(true, true, true, false, true, false, true, false),
        Char(true, false, true, false, false, true, true, false),
        Char(true, false, false, true, false, true, true, false),
        Char(true, true, true, false, false, true, true, false),
        Char(false, false, false, true, false, true, true, false),
        Char(false, false, true, false, true, true, true, false),
        Char(true, true, false, false, true, true, true, false),
        Char(false, true, false, true, true, true, false, false)) ++
    (endl ++
      maps[nat, char](((i: nat) =>
                        List(Char(false, false, false, false, false, true,
                                   false, false),
                              Char(false, false, false, false, false, true,
                                    false, false),
                              Char(true, true, true, false, true, true, true,
                                    false)) ++
                          (shows_prec_nat.apply(zero_nata).apply(i).apply(Nil) ++
                            (List(Char(false, true, false, true, true, true,
false, false),
                                   Char(false, false, false, false, false, true,
 false, false)) ++
                              (shows_prec[D](zero_nata, w(i), Nil) ++ endl)))),
                       upt.apply(zero_nata).apply(api_input_h_dim_code[A, B,
                                C](solver_input))))

def show_status[A : show, B : show, C : show](w_eq: A, err_le: B, timeout: C):
      List[char]
  =
  List(Char(true, true, false, false, true, false, true, false),
        Char(false, false, true, false, true, true, true, false),
        Char(true, false, false, false, false, true, true, false),
        Char(false, false, true, false, true, true, true, false),
        Char(true, false, true, false, true, true, true, false),
        Char(true, true, false, false, true, true, true, false),
        Char(false, true, false, true, true, true, false, false),
        Char(false, false, false, false, false, true, false, false)) ++
    (endl ++
      (List(Char(false, false, false, false, false, true, false, false),
             Char(false, false, false, false, false, true, false, false)) ++
        (List(Char(true, true, true, false, true, false, true, false),
               Char(true, false, true, false, false, true, true, false),
               Char(true, false, false, true, false, true, true, false),
               Char(true, true, true, false, false, true, true, false),
               Char(false, false, false, true, false, true, true, false),
               Char(false, false, true, false, true, true, true, false),
               Char(true, true, false, false, true, true, true, false),
               Char(false, false, false, false, false, true, false, false),
               Char(true, true, false, false, false, true, true, false),
               Char(true, true, true, true, false, true, true, false),
               Char(false, true, true, true, false, true, true, false),
               Char(false, true, true, false, true, true, true, false),
               Char(true, false, true, false, false, true, true, false),
               Char(false, true, false, false, true, true, true, false),
               Char(true, true, true, false, false, true, true, false),
               Char(true, false, true, false, false, true, true, false),
               Char(false, false, true, false, false, true, true, false),
               Char(false, true, false, true, true, true, false, false),
               Char(false, false, false, false, false, true, false, false)) ++
          (shows_prec[A](zero_nata, w_eq, Nil) ++
            (endl ++
              (List(Char(false, false, false, false, false, true, false, false),
                     Char(false, false, false, false, false, true, false,
                           false)) ++
                (List(Char(true, false, true, false, false, false, true, false),
                       Char(false, true, false, false, true, true, true, false),
                       Char(false, true, false, false, true, true, true, false),
                       Char(true, true, true, true, false, true, true, false),
                       Char(false, true, false, false, true, true, true, false),
                       Char(false, false, false, false, false, true, false,
                             false),
                       Char(false, true, false, false, false, true, true,
                             false),
                       Char(true, true, true, true, false, true, true, false),
                       Char(true, false, true, false, true, true, true, false),
                       Char(false, true, true, true, false, true, true, false),
                       Char(false, false, true, false, false, true, true,
                             false),
                       Char(false, false, false, false, false, true, false,
                             false),
                       Char(false, true, false, false, true, true, true, false),
                       Char(true, false, true, false, false, true, true, false),
                       Char(true, false, false, false, false, true, true,
                             false),
                       Char(true, true, false, false, false, true, true, false),
                       Char(false, false, false, true, false, true, true,
                             false),
                       Char(true, false, true, false, false, true, true, false),
                       Char(false, false, true, false, false, true, true,
                             false),
                       Char(false, true, false, true, true, true, false, false),
                       Char(false, false, false, false, false, true, false,
                             false)) ++
                  (shows_prec[B](zero_nata, err_le, Nil) ++
                    (endl ++
                      (List(Char(false, false, false, false, false, true, false,
                                  false),
                             Char(false, false, false, false, false, true,
                                   false, false)) ++
                        (List(Char(false, false, true, false, true, false, true,
                                    false),
                               Char(true, false, false, true, false, true, true,
                                     false),
                               Char(true, false, true, true, false, true, true,
                                     false),
                               Char(true, false, true, false, false, true, true,
                                     false),
                               Char(true, true, true, true, false, true, true,
                                     false),
                               Char(true, false, true, false, true, true, true,
                                     false),
                               Char(false, false, true, false, true, true, true,
                                     false),
                               Char(false, true, false, true, true, true, false,
                                     false),
                               Char(false, false, false, false, false, true,
                                     false, false)) ++
                          (shows_prec[C](zero_nata, timeout, Nil) ++
                            endl))))))))))))

def show_steps[A : show](steps: A): List[char] =
  List(Char(true, false, false, true, false, false, true, false),
        Char(false, false, true, false, true, true, true, false),
        Char(true, false, true, false, false, true, true, false),
        Char(false, true, false, false, true, true, true, false),
        Char(true, false, false, false, false, true, true, false),
        Char(false, false, true, false, true, true, true, false),
        Char(true, false, false, true, false, true, true, false),
        Char(true, true, true, true, false, true, true, false),
        Char(false, true, true, true, false, true, true, false),
        Char(true, true, false, false, true, true, true, false),
        Char(false, true, false, true, true, true, false, false),
        Char(false, false, false, false, false, true, false, false)) ++
    (shows_prec[A](zero_nata, steps, Nil) ++ endl)

def show_res(solver_input:
               api_input_ext[nat, (DiffArray.T[Option[real]], nat), Unit],
              x1: (nat => real,
                    (List[((Array.T[nat], nat), nat)],
                      (real, (nat, (Boolean, (Boolean, Boolean))))))):
      String
  =
  (solver_input, x1) match {
  case (solver_input, (w, (p, (err, (steps, (w_eq, (err_le, timeout))))))) =>
    implode(List(Char(false, true, false, false, true, false, true, false),
                  Char(true, false, true, false, false, true, true, false),
                  Char(true, true, false, false, true, true, true, false),
                  Char(true, false, true, false, true, true, true, false),
                  Char(false, false, true, true, false, true, true, false),
                  Char(false, false, true, false, true, true, true, false),
                  Char(false, true, false, true, true, true, false, false)) ++
              (endl ++
                (show_weights[nat, (DiffArray.T[Option[real]], nat), Unit,
                               real](solver_input, w) ++
                  (show_pol[nat](solver_input, p) ++
                    (show_err[real](err) ++
                      (show_steps[nat](steps) ++
                        show_status[Boolean, Boolean,
                                     Boolean](w_eq, err_le, timeout)))))))
}

def show_vec[A, B](v: tree[(A, B)]): List[A] = inorder[A, B](v)

def array_grow[A](a: DiffArray.T[A]): nat => A => DiffArray.T[A] =
  comp[BigInt, A => DiffArray.T[A],
        nat](((b: BigInt) => (c: A) => DiffArray.grow(a,b.toInt,c)),
              ((aa: nat) => integer_of_nat(aa)))

def iam_empty[A]: Unit => DiffArray.T[Option[A]] =
  ((_: Unit) => DiffArray.array_of_list[Option[A]](Nil))

def am_lookup[A : equal, B]: (List[(A, B)]) => A => Option[B] =
  ((a: List[(A, B)]) => (b: A) => map_of[A, B](a, b))

def vec_lookup[A]: (List[(nat, A)]) => nat => Option[A] = am_lookup[nat, A]

def iam_increment(l: nat, idx: nat): nat =
  max[nat](minus_nata(plus_nata(idx, one_nata), l),
            plus_nata(times_nata(nat_of_integer(BigInt(2)), l),
                       nat_of_integer(BigInt(3))))

def array_set_oo[A](f: Unit => DiffArray.T[A], a: DiffArray.T[A]):
      nat => A => DiffArray.T[A]
  =
  comp[BigInt, A => DiffArray.T[A],
        nat](((b: BigInt) => (c: A) => DiffArray.set_oo(f,a,b.toInt,c)),
              ((aa: nat) => integer_of_nat(aa)))

def iam_update[A](k: nat, v: A, a: DiffArray.T[Option[A]]):
      DiffArray.T[Option[A]]
  =
  (array_set_oo[Option[A]](((_: Unit) =>
                             (array_set[Option[A]]((array_grow[Option[A]](a)).apply(iam_increment(array_length[Option[A]].apply(a),
                   k)).apply(None))).apply(k).apply(Some[A](v))),
                            a)).apply(k).apply(Some[A](v))

def rat_of_real(x0: real): rat = x0 match {
  case Ratreal(x) => x
}

def g_list_to_map_iam_basic_ops[A](l: List[(nat, A)]): DiffArray.T[Option[A]] =
  foldl[DiffArray.T[Option[A]],
         (nat, A)](((m: DiffArray.T[Option[A]]) => (a: (nat, A)) =>
                     {
                       val (k, v) = a: ((nat, A));
                       iam_update[A](k, v, m)
                     }),
                    iam_empty[A].apply(()), rev[(nat, A)](l))

def pmf_from_list[A](xs: List[(nat, A)]): (DiffArray.T[Option[A]], nat) =
  (g_list_to_map_iam_basic_ops[A](xs),
    g_from_list_bs_basic_ops(map[(nat, A),
                                  nat](((a: (nat, A)) => fst[nat, A](a)), xs)))

def set_from_list: (List[nat]) => nat =
  ((a: List[nat]) => g_from_list_bs_basic_ops(a))

def divide_rat(p: rat, q: rat): rat =
  Frct({
         val (a, c) = quotient_of(p): ((int, int))
         val (b, d) = quotient_of(q): ((int, int));
         normalize((times_int(a, d), times_int(c, b)))
       })

} /* object Solver */
