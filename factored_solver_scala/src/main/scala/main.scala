import Solver._
import fastparse.MultiLineWhitespace._
import fastparse._
import org.openjdk.jmh.annotations._

import java.io.{File, PrintWriter}
import scala.language.postfixOps
import scala.sys.process._

object main {

  var lp_time: Long = 0
  var x = 0

  private type isa_tree[T] = List[(T)]
  private type rat_map = isa_tree[(nat, real)]

  private def printPoly(xs: rat_map): String = {
    def f(v: nat, c: rat): String = s"${Solver.show_rat(c)} x${Solver.show_nata(v)}"

    xs.map { case (v, c) => f(v, rat_of_real(c)) }.mkString(" + ")


  }

  private def printConstraint(c: nat, p: rat_map, b: real): String = {
    val bStr = Solver.show_rat(rat_of_real(b))
    //val bStr = Some(b) match {
    //  case Some(x) => Solver.show_rat(rat_of_real(x))
    // case None => "0"
    //}
    s"y${Solver.show_nata(c)}: ${printPoly(p)} <= $bStr"
  }

  private def lpToFile(n: nat, obj: rat_map, cs: isa_tree[((nat, rat_map))], b: rat_map): String = {
    val minStr = "Min\n"
    val cStr = printPoly(obj) + "\n"
    val st = "Subject to\n"
    val csStr = ((cs.zip(b))).map(cp => printConstraint(cp._1._1, cp._1._2, cp._2._2)).mkString("\n")
    val varStrs = (0 until (integer_of_nat(n)).toInt).toList.map(i => s"x$i")
    val boundSec = "\nBounds\n"
    val bounds = varStrs.map(v => s"$v free").mkString("\n")
    val endStr = "\nEnd\n"

    minStr +
      cStr +
      st +
      csStr +
      boundSec +
      bounds +
      endStr
  }

  private def number[$: P]: P[BigInt] = P(("-".? ~ CharIn("0-9").repX(1)).!.map(s => BigInt(s)))

  private def parse_nat[$: P]: P[nat] = number.map(nat_of_integer)

  private def parse_int[$: P]: P[int] = number.map(int_of_integer)

  private def parse_rat[$: P]: P[rat] = P((parse_int ~ ("/" ~ parse_int).?).map({ case (a, b) => Frct(a, b match {
    case Some(i) => i
    case None => int_of_integer(1)
  })
  }))

  private def vars[$: P](s: String) = P(s ~ parse_nat ~ parse_rat)

  private def parse_sol[$: P] = {
    // parse primal, then dual variables incl. their values
    vars("x").rep ~ "DUAL" ~ vars("y").rep
  }

  private def sol_to_list(sol: Seq[(nat, rat)]): List[(nat, real)] = {
    List.from(sol.sortBy(x => integer_of_nat(x._1)).map(i => (i._1, Ratreal(i._2))))
  }

  def oracle_soplex(n: nat, obj: rat_map, cs: isa_tree[(nat, rat_map)], b: rat_map): Cert_Opt[rat_map] = {

    println("Oracle called.")

    // lp as string in .lp format
    def lp_f = lpToFile(n, obj, cs, b)

    println("LP converted to string.")

    // write LP to file
    val pw = new PrintWriter(new File("isabelle_problem.lp"))
    pw.write(lp_f)
    pw.close()

    println("LP written to file")


    // solve lp using soplex
    val before = System.nanoTime
    val _ = "./oracles/soplex_wrapper.sh" !;

    lp_time = lp_time + (System.nanoTime - before)

    println("LP solver finished.")

    // read solution from file + parse
    val source = scala.io.Source.fromFile("isabelle_sol.sol")
    val lp_sol_str: String = try source.mkString finally source.close()
    val Parsed.Success(lp_sol, _) = parse(lp_sol_str, parse_sol(_))
    val (x_sol, y_sol) = lp_sol
    val x_sol_real = sol_to_list(x_sol)
    val y_sol_real = sol_to_list(y_sol)

    // return certificate
    val cert = Cert_Opt((x_sol_real), (y_sol_real))

    println("Certificate created.")

    cert
  }

  private val oracle = {
    val lp_oracle = oracle_soplex _;
    val oracle_fn =
      (a: nat) => (b: rat_map) => (c: isa_tree[(nat, rat_map)]) => (d: rat_map) => Some(lp_oracle(a, b, c, d))
    oracle_fn
  }

  def run(model: Input.Input) = {

    val input_isa = model.mk_input

    println("Isabelle input created.")

    val res = Solver.solver(input_isa)(oracle).getOrElse(throw new NoSuchElementException("Invalid input system"))

    println("Solver done.")

    println(show_res(input_isa, res))

  }

  def print_usage(): Unit = {
    println("Usage: <domain> <variables> <err_bd> <disc> <t_max>\n" +
      "\t<domain> = star | ring")
    sys.exit(1)
  }

  def main(args: Array[String]) = {
    if (args.length != 5) {
      print_usage()
    }

    println("Solver begins.")

    val time_start = System.nanoTime()


    val err_bd = parse(args(2), parse_rat(_)).get.value
    val disc = parse(args(3), parse_rat(_)).get.value
    val t_max = BigInt(args(4))
    val dims = BigInt(args(1))

    if (args(0) == "ring") {
      object Model_Ring extends Model_Ring(dims, disc, err_bd, t_max)
      val input = Model_Ring.input_network
      run(input)
    }
    else if (args(0) == "star") {
      object Model_Star extends Model_Star(dims, disc, err_bd, t_max)
      val input = Model_Star.input_network
      run(input)
    }
    else {
      print_usage()
    }

    val time_end = System.nanoTime()
    val time_total = time_end - time_start;

    println(s"Time total: ${time_total / 1e9}")
    println(s"Time in LP solver: ${lp_time / 1e9}")

  }

}

