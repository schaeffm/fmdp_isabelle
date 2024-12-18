import Input._
import Solver.{minus_rat, rat}
import rat_fns.{mk_rat, r0, r1}

class Model_Star(dims : nat, disc : rat, err_bd : rat, t_max : nat)
{
  // 0 = not working, 1 = working
  def doms(x: nat) = 2

  // action i = restart client i,
  // action dims = restart server
  // action dims + 1 = do nothing (default action)
  def actions: nat = dims + 2

  // do nothing = dims + 1
  def d: nat = dims + 1

  def server = dims

  // if action is do nothing, all computers behave as is the default
  // otherwise only computer i differs in behavior
  def effects(i: nat): Set[nat] = if (i == d) Set() else Set(i)

  // one reward function per computer, but the reward functions are the same as the default actions
  def reward_dim(i: nat): nat = if (i == d) d else 0

  // working => reward of one, not working => reward of 0
  def reward_network(j: nat): scoped_fn[rat] =
    ((s =>
      if (s(j.toInt).orNull == 0) // computer not working
        r0 // not working => reward 0
      else
        r1 // not working => reward 1
    ): state => rat, Set(j))

  // asymmetry in the rewards, server is more valuable
  def server_reward_network(j: nat): scoped_fn[rat] = {
    ((s =>
      if (s(j.toInt).orNull == 0) // computer not working
        r0 // not working => reward 0
      else
        mk_rat(2, 1) // not working => reward 2
      ): state => rat
      , Set(j)
    )
  }

  // rewards are only state-based, ignore actions
  def reward(a: nat)(i: nat): scoped_fn[rat] = {
    if (i == server)
      server_reward_network(i)
    else
      reward_network(i)
  }

  // predecessor in the ring
  // def pred(i: BigInt): nat = (i + dims - 1) % dims

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
        // (state_self, state_server)
        (s(i.toInt).get.toInt, s(server.toInt).get.toInt) match {
          case (0, 0) => ff
          case (0, 1) => tf
          case (1, 0) => ft
          case (1, 1) => tt
        }
      }, Set(i, server))
  }

  def transitions(a: nat)(i: nat): scoped_fn[pmf] = transitions_a(a, i)

  val mdp: FactoredMDP = FactoredMDP(dims + 1, doms, actions, d, effects, reward_dim, reward, transitions)

  val h_dim = d + 1

  def ind_network(i: nat): scoped_fn[rat] =
    ((s: state) =>
      (if ((s(i.toInt).get == 1)) r1 else r0), Set.from(List(i)))

  // basis functions
  // - constant function 1 to address bias
  // - function for every computer (better: combination of every computer + server?)
  def h_network(i: nat): scoped_fn[rat] = {
    if (i == h_dim - 1)
      ((s: state) => r1, Set.empty) // constant function 1
    else
      ind_network(i) // indicator function for every computer
  }

  def input_network: Input = Input(mdp, t_max, err_bd, disc, h_dim, h_network)

}