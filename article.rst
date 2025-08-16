==============================
 Single conversion steps Rocq
==============================

:authors: Quentin Corradi
:category: ???
:tags: coq
:summary: Rocq terms can be evaluated using reduction tactics. These tactics often perform a lot of reductions in one call. Although some can be controlled to some extent to do less reductions, this control doesn't allow single conversion steps to be performed easily. We provide a plugin that solves this issue for Rocq versions 9.X.X and above.

.. preview::

   There are several cases in which one would want to do single conversion steps in Rocq.
   For instance our previous article about conversion issues in Coq/Rocq features a long chain of single conversion steps demonstrating labouriously how the convertibility test algorithm works.
   At the moment the many different controllable reduction tactics can be used some extent to achieve that at the cost of learning in depth how they work, verbose use, and battling with the set tactic.
  
   We provide a simple to use plugin that solves this issue for Rocq versions 9.X.X and above.
   It can also be used as a pedagogic tool to demonstrate reductions and ease the learning curve of current reduction tactics.

.. coq::

   Fixpoint boom n :=
     match n with
     | 0 => 0
     | S k => (if Nat.eqb n 24 then 1 else 0) + boom k + boom k
     end.

   Goal boom 26 = boom 25 + boom 25.
     Fail Timeout 10 unfold boom at 1. (* intuitive tactic computes too much *)
     Fail lazy delta [boom] at 1. (* no occurence control without set *)
     (* our plugin, not compatible with the tool to show this Rocq code atm,
        does it like so:
        step delta at 1.
        or so:
        step delta boom at 1.
     *)
     lazy delta [boom].
     Fail Timeout 10 (* occurence control using set may not work *)
     set (does_not_work :=
       ( fix boom n :=
         match n with
         | 0 => 0
         | S k => (if Nat.eqb n 24 then 1 else 0) + boom k + boom k
         end
       ) 26
     ).
     set (works := _ 26). (* somehow works, don't ask me why *)
     subst works.
     Fail Timeout 10 (* not this though ¯\_(ツ)_/¯ *)
     set (does_not_work := _ 25).
   Abort.

Single step reductions are as a tactic in ltac (ltac2 TBD), and as a reduction in `Eval reduction in term.` (vernacular) / `let ... := eval reduction in term in ...` (ltac).
All examples will use the ltac tactic which supports occurence control.
The basic use is `step reduction`:

.. coq::

   Goal let f := (fun x => max x) 5 in f 4 = let x := 5 in x.
     step eta'. (* TODO swap eta and eta' *)
     step zeta. (* all visible occurences by default *)
     step delta. (* also works with primitives *)
     step fix. (* use cofix for cofixes *)
     step beta.
     step match. (* also works with primitive projections. use uip for UIP (SProp inversion) *)
     step beta at 2. (* specific occurence *)
     step fix.
     Fail step beta at 1 2. (* no overlapping occurences *)
     Fail step beta at 3. (* m0 isn't applied *)
     do 2 step beta; do 2 (step beta; step match); step match; step beta at 2.

Please note that occurences do not count inside evar bodies nor cast types.
Evar and casts can be eliminated using the `evar` and `cast` reductions.
There are also advanced reductions and way of counting occurences:

.. coq::

     Fail step fix. (* error message is a bug, failure is intended *)
     step fix'. (* make sure it is correct if you use it!!! as well as cofix' *)
     Fail Timeout 3
     repeat step fix'. (* esp. don't do this *)
	 step cbv (* next reduction of a call-by-value strategy *)
	 step cbn (* next reduction of a call-by-name strategy TODO *)
	 step lazy (* next reduction of a lazy strategy TODO *)
	 step head (* next reduction to get to a head normal form with call-by-name TODO *)
   Abort.

   Goal id (eq nat) (max (id 2) 3) 4.
     step delta id at 1. (* Only selects first occurences of "id" *)
     step delta id.
	 (* I might consider adding that for match *)
     step root. (* reduces at root of the term (TODO: rename current `head`) *)
   Abort.

There is also `eta` to eta expand the whole term, but it is not very usable on its own.
Using it with `change` or `match goal with ...` is recommended.
The last reduction is called `zeta_match` for let-bindings in match; it is safe to ignore if you don't know what that is or have not encountered it before.
