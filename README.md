# TLA+ Specification of Flexible Paxos

This repository contains the [TLA+](research.microsoft.com/en-us/um/people/lamport/tla/tla.html) specification and TLC model checking configuration for single shot [Flexible Paxos](http://drops.dagstuhl.de/opus/volltexte/2017/7094/pdf/LIPIcs-OPODIS-2016-25.pdf).

Instructions for installing and setting up TLA+ are available [elsewhere](http://research.microsoft.com/en-us/um/people/lamport/tla/tla.html). These instructions assume that you are running TLA+ from the command line using [tla-bin](https://github.com/pmer/tla-bin).

You can model check this specification by cloning this directory and running:
```
$ tlc -config MCFPaxos.cfg MCFPaxosTwoAcc.tla
```

By editing [MCFPaxosTwoAcc.tla](MCFPaxosTwoAcc.tla), you can modify the configuration to test different models. For example, you might wish to try changing the number of acceptors, how quorums are composed or the number of ballots.

This TLA+ specification is derived from [Leslie Lamport's](http://www.lamport.org) Paxos specification from [TLA+ Examples](https://github.com/tlaplus/Examples).

## The specification in Lean

The [`lean`](lean) directory contains a translation of [`FPaxos.tla`](FPaxos.tla)
to Lean 4 using the [Veil](https://github.com/verse-lab/veil) transition-system
DSL:

* [`lean/FPaxos.lean`](lean/FPaxos.lean) contains the Veil specification.
  TLA+ message sets are represented as relations, and the `-1` sentinel used
  for an acceptor with no promise or vote is represented by the
  `hasPromised` and `hasVoted` relations.
* [`lean/FPaxosProof.lean`](lean/FPaxosProof.lean) gives a corresponding
  mathematical transition relation and direct Lean proofs that proposal
  uniqueness and vote provenance hold initially and are preserved by every
  action. A reachability induction applies those preservation results to every
  protocol execution. The proof then derives one vote and one agreed value per
  ballot, followed by a `reachable_safety` theorem for every reachable state.
  These proofs do not call Veil's SMT-based `#check_invariants`.

The abstract Lean model preserves the TLA+ quorum assumption: every phase-one
quorum intersects every phase-two quorum. As in the concrete TLC models, the
proof of agreement also assumes that the phase-one quorum family is nonempty.
Lean's types enforce the `TypeOK` conditions by construction.

The proof covers the two inductive invariants declared in the Veil module and
the literal TLA+ `Safety` definition. It does not claim a proof of the stronger
TLA+ `SafeValue` property. The direct proof model is kept separate from Veil's
generated state representation so that its action cases remain readable; the
two action encodings are checked by compilation but their correspondence is
not itself a Lean theorem.

Veil and its Lean toolchain are pinned by the files in the `lean` directory.
The Veil build requires Node.js and `npm` for its editor widget. Build both the
DSL specification and the direct proofs with:

```sh
cd lean
lake update
lake build
```
