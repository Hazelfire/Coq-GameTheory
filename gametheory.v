(* This is an attempt to write theory of games and economic behaviour into Coq to prove to myself that I understand the contents *)

Require Import QArith.

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

Module FunctionalCalculus.
  (* We then need to define our functional calculus terms, min and max *)

  (* This poses our first challenge... minimum is technically a function which given a function returns another function... But it's a tad difficult when it's curried. I want to at least try though. *)
  Definition minimum_assumed_at {X: Type} (f: X -> Q) (x0:X): Prop:=
    exists m, m = f x0 /\ forall x:X, m <= f x0.

  Definition maximum_assumed_at {X: Type} (f: X -> Q) (x0:X): Prop:=
    exists m, m = f x0 /\ forall x:X, m >= f x0.

  Definition is_minimum_f {X Y: Type} (f:X -> Y -> Q) (f2 : X -> Q): Prop :=
    forall x y0, minimum_assumed_at (f x) y0 -> f2 x = f x y0. 

  Definition is_maximum_f {X Y: Type} (f:X -> Y -> Q) (f2 : X -> Q): Prop :=
    forall x y0, maximum_assumed_at (f x) y0 -> f2 x = f x y0. 

  Theorem max_max_doesnt_care_variable_order : forall (X Y: Type) (f : X -> Y -> Q) (f2: X -> Q) (f3: Y -> Q) (x0: X) (y0: Y), is_maximum_f f f2 -> maximum_assumed_at f2 x0 -> is_maximum_f (Basics.flip f) f3 -> maximum_assumed_at f3 y0 -> f2 x0 = f3 y0.
  Proof.
    intros X Y f f2 f3 x0 y0 Hmax1y Hmax1x Hmax2x Hmax2y.
    unfold is_maximum_f in Hmax1y.
    rewrite -> (Hmax1y x0 y0).
    unfold is_maximum_f in Hmax2x.
    rewrite -> (Hmax2x y0 x0).
    unfold Basics.flip. 
    reflexivity.
  Qed.
  Theorem max_min_always_smaller_min_max : forall (X Y: Type) (f : X -> Y -> Q) (f2: X -> Q) (f3: Y -> Q) (x0: X) (y0: Y), is_minimum_f f f2 -> maximum_assumed_at f2 x0 -> is_maximum_f (Basics.flip f) f3 -> minimum_assumed_at f3 y0 -> f2 x0 <= f3 y0.
  Proof.


End FunctionalCalculus.

Module StrictlyDetermined.
  (* The next goal is to define what it means to be strictly determined. A
   * strictly determined game is one where knowing the strategy before you
   * start playing the game advantages the player. *)

  (* We first determine the majorant and minorant of a given game *)
   

End StrictlyDetermined.
