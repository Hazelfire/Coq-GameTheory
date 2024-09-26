(* This is an attempt to write theory of games and economic behaviour into Coq to prove to myself that I understand the contents *)

Require Import QArith.
Require Import Coq.Structures.Orders.
Require Import Coq.Structures.OrdersTac.

Module ReducedGame.
  (* We first start by defining the concept of a reduced game. In a reduced game, all players simply specify a strategy by it's index (a natural number) and then the value function determines the expected outcome for that collection of strategies. We then go ahead and define what it means to be a 0 sum game *)
  Definition value_fn := list nat -> Q.

  Inductive ReducedGame :=
    | game (player_count: nat) (f: list value_fn).

  Definition value_fns_of_game (g: ReducedGame): list value_fn :=
    match g with
    | game _ f => f
    end.

  Definition list_q_sum (l: list Q) : Q := List.fold_left Qplus l 0.

  Definition sum_of_game (g: ReducedGame) (strategies: list nat) := 
    list_q_sum (List.map (fun f => f strategies) (value_fns_of_game g)).

  Definition game_is_zero_sum (g: ReducedGame) := forall s: list nat, sum_of_game g s = 0.

  Inductive ZeroSumGame :=
    | zeroSumGame (g: ReducedGame) (t: game_is_zero_sum g).
End ReducedGame.

Module Type MinMax( E:TotalOrder').
  Import E. 
  Parameter X : Type.
  Parameter min : (X -> t) -> t.
  Axiom min_exists :
    forall f, exists x0, min f = f x0.
  Axiom min_is_minimum : forall f x, min f <= f x.
  Parameter max : (X -> t) -> t.
  Axiom max_exists :
    forall f, exists x0, max f = f x0.
  Axiom max_is_maximum : forall f x, f x <= max f.
End MinMax.

Module FunctionalCalculus (MinMaxMod : MinMax) (E:TotalOrder').
  Module EMinMaxMod := MinMaxMod(E). 
  Import EMinMaxMod. 
  Import E.
  Module OrderTac := MakeOrderTac(E)(E).  
  Import OrderTac.

  Lemma le_trans : forall a b c, a <= b -> b <= c -> a <= c.
  Proof.
    order. 
  Qed.


  (* First we prove that if you find the minimum over two variables,
     it must necesarily be the minimum of the bivariate function *)
  Lemma min_min_is_min_of_both : forall (f: X -> X -> t) x y, min (fun x => min (f x)) <= (f x y).
  Proof.
    intros f x y. 
    apply (le_trans (min (fun x => min (f x))) (min (f x)) (f x y)).
    - apply (min_is_minimum (fun x => min (f x)) x). 
    - apply min_is_minimum. 
  Qed.

  Lemma lower_a_b_eq : forall a b, a <= b -> b <= a -> b == a.
  Proof.
    order. 
  Qed.


  (* Therefore this means that the both the left and the right of this
     are lower than or equal to all f x y, hence lower than or equal
     to each other, hence equal *)
  Theorem min_min_commutative : forall (f: X -> X -> t), min (fun x => min (f x)) == min (fun x => min (Basics.flip f x)).
  Proof.
    intros f.
    apply lower_a_b_eq. 
    - destruct (min_exists (fun x => min (f x))) as [y0r ->].
      destruct (min_exists (f y0r)) as [x0r ->].
      fold ((Basics.flip f) x0r y0r). 
      apply min_min_is_min_of_both. 
    - destruct (min_exists (fun x : X => min (Basics.flip f x))) as [y0r ->].
      destruct (min_exists (Basics.flip f y0r)) as [x0r ->].
      unfold Basics.flip. 
      apply min_min_is_min_of_both. 
  Qed.

  (* Same argument goes for maximum *)
  Lemma max_max_is_max_of_both : forall (f: X -> X -> t) x y, (f x y) <= max (fun x => max (f x)).
  Proof.
    intros f x y. 
    apply (le_trans (f x y) (max (f x)) (max (fun x0 : X => max (f x0))) ).
    - apply max_is_maximum.
    - apply (max_is_maximum (fun x => max (f x)) x). 
  Qed.

  Theorem max_max_commutative : forall (f: X -> X -> t), max (fun x => max (f x)) == max (fun y => max (Basics.flip f y)).
  Proof.
    intros f.
    apply lower_a_b_eq. 
    - destruct (max_exists (fun y : X => max (Basics.flip f y))) as [y0r ->].
      destruct (max_exists (Basics.flip f y0r)) as [x0r ->].
      unfold Basics.flip. 
      apply max_max_is_max_of_both. 
    - destruct (max_exists (fun x => max (f x))) as [y0r ->].
      destruct (max_exists (f y0r)) as [x0r ->].
      fold (Basics.flip f x0r y0r). 
      apply max_max_is_max_of_both. 
  Qed.


  (* Now we can discuss saddle points of bivariate functions, where x0 is the
  maximums of all xs and y0 is the minimum of all y *)
  (* saddle points may not exists, but if they do, they have this property *)
  Definition saddle_point (f: X -> X -> t) (x0 y0:X) := min (f x0) = f x0 y0 /\ max (fun x' => f x' y0) = f x0 y0. 

  Lemma saddle_value_unique : forall (f: X -> X -> t) (x0 y0 x0' y0': X), saddle_point f x0 y0 -> saddle_point f x0' y0' -> f x0 y0 == f x0' y0'.
  Proof.
  intros f x0 y0 x0' y0' [minf0 maxf0] [minf0' maxf0']. 
  apply lower_a_b_eq. 
  - rewrite <- maxf0. 
    rewrite <- minf0'.  
    apply le_trans with (f x0' y0). 
    + apply min_is_minimum. 
    + apply (max_is_maximum (fun x' : X => f x' y0)). 
  - rewrite <- maxf0'.
    rewrite <- minf0. 
    apply le_trans with (f x0 y0'). 
    + apply min_is_minimum. 
    + apply (max_is_maximum (fun x' : X => f x' y0')). 
  Qed.



    .



End FunctionalCalculus.

Module StrictlyDetermined.
  (* The next goal is to define what it means to be strictly determined. A
   * strictly determined game is one where knowing the strategy before you
   * start playing the game advantages the player. *)

  (* We first determine the majorant and minorant of a given game *)
   

End StrictlyDetermined.
