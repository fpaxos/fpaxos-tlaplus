# TLA+ Specification of Flexible Paxos

This repository contains the [TLA+](research.microsoft.com/en-us/um/people/lamport/tla/tla.html) specification and TLC model checking configuration for single shot [Flexible Paxos](http://drops.dagstuhl.de/opus/volltexte/2017/7094/pdf/LIPIcs-OPODIS-2016-25.pdf).

Instructions for installing and setting up TLA+ are available [elsewhere](http://research.microsoft.com/en-us/um/people/lamport/tla/tla.html). These instructions assume that you are running TLA+ from the command line using [tla-bin](https://github.com/pmer/tla-bin).

You can model check this specification by cloning this directory and running:
```
$ tlc -config MCFPaxos.cfg MCFPaxosTwoAcc.tla
```

By editing [MCFPaxosTwoAcc.tla](MCFPaxosTwoAcc.tla), you can modify the configuration to test different models. For example, you might wish to try changing the number of acceptors, how quorums are composed or the number of ballots.

This TLA+ specification is derived from [Leslie Lamport's](http://www.lamport.org) Paxos specification from [TLA+ Examples](https://github.com/tlaplus/Examples).
