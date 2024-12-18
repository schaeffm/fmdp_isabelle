import Input._
import Solver.{minus_rat, rat}
import rat_fns.{mk_rat, r0, r1}

class Model_Ring(dims : nat, disc : rat, err_bd : rat, t_max : nat)
{
  // 0 = not working, 1 = working
  def doms(x: nat) = 2

  // action i = restart computer i, action dims = do nothing (default action)
  def actions: nat = dims + 1

  // do nothing
  def d: nat = dims

  // if action is do nothing, all computers behave as is the default
  // otherwise only computer i differs in behavior
  def effects(i: nat): Set[nat] = if (i == dims) Set() else Set(i)

  // one reward function per computer, but the reward functions are the same as the default actions
  def reward_dim(i: nat): nat = if (i == dims) dims else 0

  // working => reward of one, not working => reward of 0
  def reward_network(j: nat): scoped_fn[rat] = ((s => if (s(j.toInt).orNull == 0) r0 else r1): state => rat, Set(j))

  // asymmetry in the rewards, last computer is more valuable
  def other_reward_network(j: nat): scoped_fn[rat] = {
    ((s =>
      if (s(j.toInt).orNull == 0)
        r0
      else mk_rat(2, 1)): state => rat
      , Set(j)
    )
  }

  def reward(a: nat)(i: nat): scoped_fn[rat] = {
    if (i == dims - 1)
      other_reward_network(i)
    else
      reward_network(i)
  }

  // predecessor in the ring
  def pred(i: BigInt): nat = (i + dims - 1) % dims

  // 0.0238
  val p_ff = mk_rat(238, 10000)

  val p_ft = mk_rat(475, 1000)

  val p_tf = mk_rat(475, 10000)

  val p_tt = mk_rat(95, 100)

  val ff = pmf_network(p_ff)
  val tf = pmf_network(p_tf)
  val ft = pmf_network(p_ft)
  val tt = pmf_network(p_tt)

  def pmf_network(p_true: rat): List[(nat, rat)] = List((0, minus_rat(r1, p_true)), (1, p_true))

  def transitions_a(a: nat, i: nat): scoped_fn[pmf] = {

    // Machine i restarted, certainly is on
    if (a == i)
      ((_: state) => pmf_network(r1), Set[nat]())
    else
      ((s: state) => {
        (s(i.toInt).get.toInt, s(pred(i).toInt).get.toInt) match {
          case (0, 0) => ff
          case (0, 1) => tf
          case (1, 0) => ft
          case (1, 1) => tt
        }
      }, Set(i, pred(i)))
  }

  def transitions(a: nat)(i: nat): scoped_fn[pmf] = transitions_a(a, i)

  val mdp: FactoredMDP = FactoredMDP(dims, doms, actions, d, effects, reward_dim, reward, transitions)

  val h_dim = dims + 1

  def ind_network(i: nat): scoped_fn[rat] =
    ((s: state) => if (s(i.toInt).get == 0) r0 else r1, Set.from(List(i)))

  def h_network(i: nat): scoped_fn[rat] = {
    if (i == dims)
      ((s: state) => r1, Set.empty)
    else
      ind_network(i)
  }

  def input_network: Input = Input(mdp, t_max, err_bd, disc, h_dim, h_network)

}
