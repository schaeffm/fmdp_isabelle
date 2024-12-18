import Solver.{Fract, Nat, Ratreal, api_input_ext, api_input_exta, equal_rat, int_of_integer, integer_of_nat, minus_rat, nat, nat_of_integer, pmf_from_list, rat, real}

object rat_fns {
  def mk_rat(i: BigInt, j: BigInt): rat = {
    Fract(int_of_integer(i), int_of_integer(j))
  }

  def rat_of_int(i: BigInt) = mk_rat(i, 1)

  val r1 = rat_of_int(1)

  val r0 = rat_of_int(0)
}

object Input {
  type nat = BigInt
  type state = Vector[Option[nat]]
  type nat_set = Set[nat]
  type pmf = List[(nat, rat)]
  type scoped_fn[out] = (state => out, nat_set)
  type isa_nat = Solver.nat
  type isa_nat_set = Solver.nat
  type isa_pmf =  (DiffArray.T[Option[real]], isa_nat_set)
  type input_ext = Unit
  type input = api_input_ext[isa_nat_set, isa_pmf, input_ext]
  type isa_scoped_fn[out] = Solver.Scoped_Tree[out]

  case class FactoredMDP(
                          dims: nat,
                          doms: nat => nat,

                          actions: nat,
                          d: nat,
                          effects: nat => nat_set,

                          reward_dim: nat => nat,
                          rewards: nat => nat => scoped_fn[rat],

                          transitions: BigInt => BigInt => scoped_fn[pmf]
                        ) {

    def scoped_fn_to_tree[A](f: state => A, s: nat_set): Solver.Scoped_Tree[A] = {
      def scoped_fn_to_tree_aux(s: nat_set, x: state): Solver.Scoped_Tree[A] = {
        if (s.isEmpty)
          Solver.Scoped_Leaf(f(x))
        else {
          val i = s.head

          val s_new = s.tail

          def rec_call(y: Solver.nat): Solver.Scoped_Tree[A] = scoped_fn_to_tree_aux(s_new,
            x.updated(i.toInt, Some(integer_of_nat(y))))

          val arr = Solver.of_fun(rec_call, nat_of_integer(doms(i)): Solver.nat)

          Solver.Scoped_Node(nat_of_integer(i), arr)
        }
      }

      scoped_fn_to_tree_aux(s, Vector.tabulate(dims.toInt)((i: Int) => None))
    }

    def set_to_isa_set(s : nat_set) : isa_nat_set = {
      Solver.set_from_list(s.toList.map(nat_of_integer))
    }

    val effects_isa_arr : Vector[isa_nat_set] = {
      Vector.tabulate(actions.toInt)((i : Int)  => set_to_isa_set(effects(i)))
    }

    def effects_isa(i : isa_nat) : isa_nat_set = {
      effects_isa_arr(integer_of_nat(i).toInt)
    }

    val rewards_isa_arr : Vector[Vector[isa_scoped_fn[real]]] = {
      Vector.tabulate(actions.toInt)((a : Int) =>
        Vector.tabulate(reward_dim(a).toInt)((i : Int) => {
          val r = rewards(a)(i)
          val f: isa_scoped_fn[real] = scoped_fn_to_tree((x: state) => Ratreal(r._1(x)): real, r._2)
          f
        }))
    }

    def rewards_isa(a : isa_nat)(i : isa_nat) : isa_scoped_fn[real] = {
      rewards_isa_arr(integer_of_nat(a).toInt)(integer_of_nat(i).toInt)
    }

    val rewards_scopes_arr: Vector[Vector[isa_nat_set]] = {
      Vector.tabulate(actions.toInt)((a: Int) =>
        Vector.tabulate(reward_dim(a).toInt)((i: Int) => {
          set_to_isa_set(rewards(a)(i)._2)
        }))
    }
    def rewards_scopes(a : isa_nat)(i : isa_nat) = {
      rewards_scopes_arr(integer_of_nat(a).toInt)(integer_of_nat(i).toInt)
    }

    def reward_dims(a: isa_nat) : isa_nat = {
      nat_of_integer(reward_dim(integer_of_nat(a)))
    }

    val actions_isa : isa_nat = nat_of_integer(actions)

    val dims_isa : isa_nat = nat_of_integer(dims)


    val doms_isa_arr: Vector[isa_nat] = {
      Vector.tabulate(dims.toInt)((i: Int) => nat_of_integer(doms(i)))
    }

    def doms_isa(i : isa_nat) : isa_nat = doms_isa_arr(integer_of_nat(i).toInt)

    val d_isa = nat_of_integer(d)

    val transitions_isa_arr: Vector[Vector[isa_scoped_fn[isa_pmf]]] =
      Vector.tabulate(actions.toInt)((a: Int) =>
        Vector.tabulate(dims.toInt)((i: Int) => {
          val r = transitions((a))((i))

          val f = scoped_fn_to_tree((x: state) =>
            Solver.pmf_from_list(r._1(x).map(nr => (nat_of_integer(nr._1), Ratreal(nr._2): real))), r._2)
          f
        }))

    def transitions_isa(a: isa_nat)(i: isa_nat): isa_scoped_fn[isa_pmf]  = {
      transitions_isa_arr(integer_of_nat(a).toInt)(integer_of_nat(i).toInt)
    }


    val transitions_scopes_arr: Vector[Vector[isa_nat_set]] =
      Vector.tabulate(actions.toInt)((a: Int) =>
        Vector.tabulate(dims.toInt)((i: Int) => {
          set_to_isa_set(transitions(a)(i)._2)
        }))


    def transitions_scopes(a: isa_nat)(i: isa_nat): isa_nat_set = {
      transitions_scopes_arr(integer_of_nat(a).toInt)(integer_of_nat(i).toInt)
    }


  }

  case class Input(
                    // Model
                    mdp: FactoredMDP,

                    // Parameters
                    t_max: BigInt,
                    eps: rat,
                    l: rat,

                    // Basis
                    h_dim: BigInt,
                    h: BigInt => scoped_fn[rat]
                  )
  {

    val h_arr: Vector[isa_scoped_fn[real]] = {
      Vector.tabulate(h_dim.toInt)((i: Int) => {

        val r = h(i)

        val f = mdp.scoped_fn_to_tree((x: state) =>
          Ratreal(r._1(x)): real, r._2)

        f
      })
    }

    def h_isa(i: isa_nat): isa_scoped_fn[real] = {
      h_arr(integer_of_nat(i).toInt)
    }

    val h_scope_arr: Vector[isa_nat_set] = {
      Vector.tabulate(h_dim.toInt)((i: Int) => mdp.set_to_isa_set(h(i)._2))
    }

    def h_scope_isa(i: isa_nat) = {
      h_scope_arr(integer_of_nat(i).toInt)
    }

    val h_dim_isa: isa_nat = nat_of_integer(h_dim)

    val mk_input: input = {

      val t_max_isa = nat_of_integer(t_max)
      val epsilon_isa = Ratreal(eps)
      val l_isa = Ratreal(l)

      api_input_exta(
        mdp.dims_isa,
        mdp.doms_isa,
        t_max_isa,
        epsilon_isa,
        mdp.rewards_isa,
        mdp.rewards_scopes,
        mdp.reward_dims,
        mdp.actions_isa,
        mdp.d_isa,
        mdp.transitions_isa,
        mdp.transitions_scopes,
        l_isa,
        h_isa,
        h_scope_isa,
        h_dim_isa,
        mdp.effects_isa,
        ()
      )
    }
  }
}

