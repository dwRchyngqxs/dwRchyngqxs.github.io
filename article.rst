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
