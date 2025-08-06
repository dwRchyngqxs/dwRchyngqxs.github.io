===================================
 Convertibility issues in Coq/Rocq
===================================

:authors: Quentin Corradi
:category: ???
:tags: coq
:summary: Coq/Rocq uses an algorithm with heuristics to test convertibility of terms. While these heuristics work fine for a class of problems, some simple convertibility problems can make it take forever to arrive to an answer. Usually these problems are posed by testing convertibility of terms which were obtained by explicitly converting the term so are convertible. We propose to add a convertibility checker that takes a convertibility certificate to efficiently validate convertibility in such cases.

.. preview::

  A proof that passes can take forever at Qed time because of convertibility tests.
  Our proposed solution to this issue is to replay computations instead of relying on heuristics.

.. coq::

   Fixpoint boom n :=
     match n with
     | 0 => 0
     | S k => (if Nat.eqb n 24 then 1 else 0) + boom k + boom k
     end.

   Goal 1 + (boom 23 + 1) = (1 + boom 23) + 1.
   Proof.
     Time cbn -[boom]. (* immediate, should be replayed by Qed *)
     Time reflexivity. (* immediate *)
   Time Qed. (* takes forever *)

Coq/Rocq has a notion of computation using sequences of simple rewrites called reductions.
A term can be partially evaluated is considered definitionally equal to the result of the evaluation, that is, it is supposed to be considered the same.
For instance terms like `1 + 1` and `2` are usable indistinguishibly:

.. coq::

   Require Coq.Vectors.Vector.
   Arguments Vector.cons {A} _ {n}.

   Check Vector.cons true (Vector.cons false (Vector.nil bool)). (* 2 *)

   (* 2 used in place of 1 + 1 *)
   Definition sample: Vector.t bool (1 + 1) :=
     Vector.cons true (Vector.cons false (Vector.nil bool)).

   Check sample. (* 1 + 1 *)

Such indistinguishable terms are called convertible_.
Informally convertible terms are terms that can be transformed into one another with a sequence of conversions_ (or their reverse rewrite).
The intuition behind convertibility is that because of strong normalisation, convertible terms eventually reduce to the same normal form no matter in which order reductions are performed, and these terms should all be considered equal to that normal form.
Checking for convertibility between terms is decidable thanks to strong normalisation as reducing both terms to a normal form and checking for equality is sufficient.
However it is not always efficient nor practical to do so:

.. _convertible: https://rocq-prover.org/doc/V9.0.0/refman/language/core/conversion.html#convertibility
.. _conversions: https://rocq-prover.org/doc/V9.0.0/refman/language/core/conversion.html

.. coq::

   Goal boom 26 = boom 25 + boom 25.
   Proof.
     Time vm_compute. (* reduces fast until normal form *)
     reflexivity.
   Time Qed. (* also reduces fast until normal form *)

In practice to validate convertibility, reducing to a common term is more efficient.
However this isn't sufficient to validate non convertibility as two different terms are not necessarily non convertible, they might just not be reduced to normal form.
Validating that two terms (not necessarily normal form) are not convertible requires reducing them until the head of the term cannot be reduced anymore (is stuck), then they are not convertible if their root doesn't match or if any direct subterm of one term's root is not convertible with the corresponding direct subterm of the other term.
So an algorithm that checks for convertibility between two terms not necessarily in normal form, without reducing them, will either answer with the convertibility of the terms, or answer that the terms are not reduced enough to decide.
Below are examples of convertibility problems on not fully reduced terms which showcase both convertibility and decidability without reduction:

* Decidable and convertible:

  `fun x => fib (2 + x)` -- `fun x => fib (2 + x)`

* Not decidable, head is stuck then next head is not.
  Who knows what the definition of fib is without reducing it?

  `fun x => fib (2 + x)` -- `fun x => fib x + fib (1 + x)`

* Decidable and not convertible, a fun is definitely not a Vector.cons (stuck, it is a constructor):

  `fun x => fib (2 + x)` -- `Vector.cons (1 + 1 =? 2) Vector.nil`

Let's call this convertibility check without reduction "immediate convertibility".
A convertibility checking algorithm can therefore solve convertibility problems as follows:
Given to terms, find two sequences of reductions that reduces them to terms which immediate convertibility is decidable.

The algorithm used by Coq/Rocq does this with heuristics to decide which term to reduce, and which reduction to apply on which subterm:
First, both terms are reduced to beta-zeta-iota weak head normal form (βζι-whnf), not to be confused with and normal form.
That is the head of terms is reduced using beta, zeta, and iota reductions (all except delta) until it is stuck, which means it can either be delta reduced or it is truly stuck.
Second, the reduced terms are tested for immediate convertibility.
If immediate convertibility did not decide then either
* the head of both terms are stuck: the algorithm is applied recursively on all subterms which prevented decidability of the immediate convertibility;
* the head of only one of the term is not stuck: that term is put in whnf (with delta) and the algorithm is reapplied on the obtained terms;
* the head of both terms aren't stuck and they are different global names: an oracle decides which head to delta reduce then the algorithm is reapplied on the obtained terms;
* the head of both terms aren't stuck and they are the same global name: do as if both head were stuck, and if any of the subterm is not convertible then do as if both head aren't the same global;

This algorithm uses several tricks to try to be efficient.
The first one is to be merged with the immediate convertibility check so that reduction can be applied where the check failed.
The second one is to immediately start reducing both terms by putting them in weak head beta-zeta-iota normal form in order to detect non convertibility quicker.
The third one is to not perform delta reductions and assume that if the head are the same then it is more likely that the rest of the term prevents the immediate convertibility check from deciding.
The second and third tricks are the main heuristics the algorithm employs.
They can be really effective at cutting down computations compared to fully reducing terms:

.. coq::

   (* Simulating what convertibility test would do *)
   Goal length (1 :: 2 :: 3 :: 4 :: nil) = 1 + length (2 :: 3 :: 4 :: nil).
     (* already in beta zeta iota weak head normal form *)
     (* head do not match, oracle decides to delta reduce left *)
     set (to_reduce := length (1 :: 2 :: 3 :: 4 :: nil)).
     lazy delta [length] in to_reduce.
     (* put in beta zeta iota whnf *)
     lazy beta zeta fix in to_reduce; lazy match in to_reduce.
     subst to_reduce.
     (* head do not match, left head is fully stuck, put right in whnf *)
     set (to_reduce := 1 + length (2 :: 3 :: 4 :: nil)).
     lazy beta zeta iota delta [plus] in to_reduce.
     (* head S matches, no immediate convertibility of
       (delta expanded length) vs length,
       left head is fully stuck, put right in whnf *)
     lazy beta delta [length] in to_reduce.
     subst to_reduce.
     (* terms are immediately convertible *)
   Abort.

   (* Assuming a perfect oracle *)
   Goal boom 26 = boom 25 + boom 25.
     (* already in beta zeta iota weak head normal form  *)
     (* head do not match, oracle decides to delta reduce left *)
     set (to_reduce := boom 26).
     lazy delta [boom] in to_reduce.
     (* put in beta zeta iota whnf *)
     lazy beta zeta fix in to_reduce; lazy match in to_reduce.
     subst to_reduce.
     (* head + matches, last argument are treated first,
       (delta expanded boom) 25 vs boom 25: no immediate convertibility,
       recursive call, put in beta zeta iota whnf *)
     set (to_reduce := _ 25) at 3;
       lazy beta zeta fix in to_reduce; lazy match in to_reduce;
       subst to_reduce.
     (* head do not match, oracle decides to delta reduce right *)
     set (to_reduce := boom 25) at 2.
     lazy delta [boom] in to_reduce.
     (* put in beta zeta iota whnf *)
     lazy beta zeta fix in to_reduce; lazy match in to_reduce.
     subst to_reduce.
     (* last argument are immediately convertible, return result *)
     set (convertible := (if Nat.eqb 25 24 then 1 else 0) + _ 24 + _ 24).
     (* back at head + matches, first argument are treated next,
       no immediate convertibility of
       (if Nat.eqb 26 24 then 1 else 0) + (delta expanded boom) 25 vs boom 25,
       recursive call, already in beta zeta iota whnf
       head do not mach, oracle decides to delta reduce left *)
     set (to_reduce := plus) at 2; lazy delta [plus] in to_reduce; subst to_reduce.
     (* already in whnf, new head is Nat.eqb,
       doesn't match +, oracle decides to delta reduce left *)
     set (to_reduce := if Nat.eqb 26 24 then 1 else 0).
     lazy delta [Nat.eqb] in to_reduce.
     (* put in beta zeta iota whnf *)
     lazy beta zeta iota in to_reduce.
     subst to_reduce.
     (* still not whnf, I wish I could control reduction without all these set/subst ;) *)
     set (to_reduce := _ 0);
       lazy beta zeta fix in to_reduce; subst to_reduce; lazy beta match;
       set (to_reduce := _ 25) at 1;
       lazy beta zeta fix in to_reduce; lazy match in to_reduce;
       subst to_reduce.
     (* head do not match, ...
       I skip this because we already did it above, terms are convertible.
       The algorithm would have to do it again though. *)
   Abort.

   (* In reality, the oracle isn't this smart enough *)
   Goal boom 26 = boom 25 + boom 25.
     Timeout 30 reflexivity.
   Abort.

While this algorithm works well for these cases, I have some remarks about the heuristics.
First, I do not know yet how the oracle works and did not investigate, let's assume for the rest of this post that it makes optimal choices.
Second, the whnf is mainly justified by a significantly reduced amount of computation to expose a stuck term at the head compared to other reduction strategies.
The reduction used by the whnf are justified by the third heuristics.
Because iota reduction is the main driving force behind recursion, it would be expected to avoid them in the whnf.
Same for zeta and beta which can make the term explode in size.
Well, it turns out this choice is not as arbitrary as it may seem.
The head of both terms has to be equal for the third heuristics to apply, requiring them be compared everytime the whnf is stuck.
The result of this check cannot be cached as the head is immediately reduced if the test fails.
So the check has to be fast, only names can be compared quickly; iota would leave a fix, beta a lambda, zeta a let binding, all of which require an expensive term comparison.
Third, when subterms are tested for convertibility as part of the third trick and one of the test fails, none of the intermediate convertibility results or reduced terms are kept.
This lead to significant duplicate computations.
I think this is a potential improvement to the current algorithm.
Finally, the third heuristics can trigger many convertibility checks of non convertible terms which require significant amout of computation to get to a result -even if all the computations were cached- leading to more computations than fully reducing both terms using an efficient strategy.
This, together with the potentially wrong choices of the oracle, are in my opinion the main source of Qed taking forever to pass.
Here is an example exploiting this flaw of the algorithm to force it to spend time in checking convertibility of non convertible terms while the overall terms are convertible using a few reductions:

.. coq::

   Definition apply [T U] f (x: T): U := f x.

   (* iter forces the full reduction of n to decide non convertibility *)
   Fixpoint iter [T] x n f: T :=
     match n with
     | O => x
     | S n => iter (f x) n f
     end.

   Goal apply (fun _ => apply (fun n => iter O n) (boom 25)) (boom 26)
      = apply                 (fun n => iter O n) (boom 25).
     set (p := apply) at 1.
     unfold apply in p. (* delta *)
     subst p.
     cbv beta. (* 3 beta *)
     reflexivity. (* and that's it *)
     (* can the convertibility algorithm figure this out? *)
     Fail Timeout 60 Qed. (* no *)
   Abort.

In the above example we use the assumption of the third trick that the head are equal (both `apply`) to trick the algorithm into deciding the convertibility of either `boom 26` with `boom 25` or `fun _ => apply (fun n => iter O n) (boom 25)` with `fun n => iter O n`.
The first convertibility check cannot be decided before fully computing `boom 25`, the second one cannot be decided before fully computing `apply (fun n => iter O n) (boom 25)` because of the definition of `iter` hinding the head constructor behind the full computation of `boom 25`.
So in both cases it takes forever, "forever" defined as the time it takes to compute `boom 25`.

This algorithm is essential to check convertibility especially when the convertibility of the terms given is unknown.
But in most cases of Qed taking forever, the convertibility problems in Qed are generated by reduction tactics.
These terms are therefore known to be convertible, and Qed should only check that they are.
This could be done even more efficiently if the reduction tactic provided a certificate that Qed only had to check.
If the certificate is invalid the proof fails, not meaning that some terms are not convertible but that the certificate are invalid.
This is our proposal to solve almost all slow and never ending Qed.

Because two convertible terms can be transformed into one another with a sequence of conversions, a certificate of convertibility can be that sequence of conversion.
A certificate checker would only have to replay the transformation on the first term and verify that the obtained term is the second one.
The representation of the conversions is important for the checker to be able to replay them.
One could imagine for instance representing the certificate as a sequence of terms.
I raise this possibility as it would not require modifying the Coq/Rocq core verified parts but only add more casts on reduction.
Each term would have to be checked for convertibility with the next one, so it would need to avoid never ending convertibility problems.
The usual reduction tactics are unlikely to go through such a sequence of terms, and finding this sequence would be complicated.
I highly doubt it is possible, even though I'm too lazy to come up with a counter example.
Another way to represent conversions can be to explicit which conversion to apply and where in the term.
The certificate checker would then only need to go to the specified place and apply the conversion, not relying on anything untrusted or potentially taking forever.

Conversions are made of reductions and their inverse, expansions.
Given a term and a location, a given kind of reduction usually has a single resulting term, while expansions have many.
This means that representing an expansion require more than a location and the name of the kind of expansion.
This information is usually as big as the term being expanded, meaning that the size of a sequence of length `n` of expansions on a term of length `m` is on the order of `n.m`.
In contrast specifying the resulting term and the inverse of the sequence of expansions will give a sequence of size on the order of `n + m`.
So instead of a sequence of conversions, a certificate is better represented as a sequence of triplets `(t1, rl1, rr1), ..., (tn, rln rrn)` where for each `k`, `tk` is a term, and `rlk` and `rrk` are sequences of reductions.
Starting from term `t0` to get to term `tn` is done by successively reducing to a common term `t[k-1]` and `tk` with `rlk` and `rrk` respectively at step `k`.
Alternatively a single sequence of reduction and a mark for which term to reduce to the other is possible requires writing more terms including the common reduction term of the triplet which tend to be bigger because of delta reduction.
This way of representing convertibility problem basically exchanges one arbitrary conversions to a sequence of convertibility problems where only reductions are allowed.
Coq/Rocq can already represent a sequence of convertibility problems with nested casts.
The only part left to figure out is how to represent a sequence of reductions.

In the previous paragraph is mentionned that given a term and a location, a given kind of reduction "usually" has a single resulting term.
"Usually" has one exceptions in Coq/Rocq:
In match patterns, variables can bind to the value set by let bindings in a type definition as shown by the example below.
Because of this, zeta reductions, usually eliminating let bindings, can be applied to match potentially without modifying to the term.
This use of zeta need to be provided with a way to identify the concerned let binding.
Even though one could expect this to be purely syntactical (it could be), it is actually part of the kernel terms and cannot be ignored.
This exception is an argument to remove let bindings in match from the Coq/Rocq kernel terms and move it to a purely syntactical construct, if developpers are reading this, please consider it.
Zeta rule is also an exception (although not the only one) for a nice property which could have further simplified the representation of reductions.
In calculus of constructions, for any given subterm there is at most one reduction possible at the root of the subterm.
The exception to that property is eta reduction, which doesn't matter because the immediate convertibility check can be modified to infer eta expansion.
If that property held in Coq/Rocq, only a sequence of location would have been enough to describe a seqence of reductions.
Unfortunately Coq/Rocq also feature reduction rules, an experimental extension allowing the expression of arbitrary rewrite rules without much constraint on the expressed rewrite, their impact on reduction and on typing.
So a reduction is a pair of a location and a reduction kind, with aditional data for the zeta reduction.
The final missing part of the picture is how to represent a location in a term.

.. coq::

   Inductive VLB := vlb: let vlbI := I in VLB.
   Record RLB := rlb { rlbI := I }.

   Definition match_vlbI :=
     match vlb with
     | vlb x => x
     end.

   Definition match_rlbI :=
     match rlb with
     | rlb x => x
     end.

   (* more usual syntax *)
   Definition match_rlbI' :=
     match rlb with
     | {| rlbI := x |} => x
     end.

Terms are trees, so a location in a term can be expressed as a location in a tree.
However, there is a more efficient representation relying on how common reduction strategies operate.
Common reduction strategies don't move randomly in a term, in fact they do quite the opposite, they tend to focus on a subterm, do several reductions at the same place, then once they unfocus the subterm, they do not focus on it again.
So they overall change location less often than they reduce, and these changes in location are very local.
Which makes full tree location wasteful compared to relative movements.
A sequence of reductions is then a sequence of either movements toward the root, movements toward a leaf, or reduction kinds with aditional data for the zeta reduction.
This sequence is easy to replay with a zipper, and easy to record using inversion of control.
Inversion of control has the added benefit of making reduction algorithms correct, although the set of reductions has to be carefully crafted to allow reductions similar to the ones performed as common optimisations.
For instance replacing a single variable from context instead of a full beta or zeta reduction is a common optimisation.
