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

The [`lean`](lean) directory contains a pure Lean 4 translation of
[`FPaxos.tla`](FPaxos.tla). [`lean/FPaxos.lean`](lean/FPaxos.lean) defines the
state, initial-state predicate, and the four protocol actions as an inductive
transition relation. TLA+ message sets are represented as predicates, while
the `-1` sentinel for an acceptor with no promise or vote is represented by
`Option.none`.

[`lean/Proof.lean`](lean/Proof.lean) proves proposal uniqueness, vote
provenance, and the protocol's required promise/history facts initially and
after every action. Phase-two proposals carry finite recursive phase-one
certificates. Together with quorum intersection, these certificates prove the
literal TLA+ `SafeValue` property even when a lower ballot becomes agreed
after a higher proposal already exists. A reachability induction yields
`reachable_safeValue` and `reachable_safety` for every reachable state. The
development uses no SMT solver or external proof framework.

The abstract Lean model preserves the TLA+ quorum assumption: every phase-one
quorum intersects every phase-two quorum. As in the concrete TLC models, the
proof of agreement also assumes that the phase-one quorum family is nonempty.
Lean's types encode a well-typed refinement of `TypeOK` by construction; in
particular, an accepted ballot and its value are present or absent together.
Ballots are represented directly as integers, matching their representation
and ordering in TLA+.

The proof covers the literal TLA+ `NoFutureProposal`, `SafeValue`, and
`Safety` definitions.

The Lean toolchain is pinned in the `lean` directory. Build the specification
and proofs with:

```sh
cd lean
lake build
```
