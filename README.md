# TLA+ Specification of Flexible Paxos

This repository contains the [TLA+](research.microsoft.com/en-us/um/people/lamport/tla/tla.html) specification and model checking setup for single valued Flexible Paxos.

Instructions for installing and setting up TLA+ are available [elsewhere](http://research.microsoft.com/en-us/um/people/lamport/tla/tla.html). These instructions assume that you are running TLA+ from the command line using [tla-bin](https://github.com/pmer/tla-bin).

You can check this specification by cloning this directory and running:
```
tlc MCFPaxos.tla
```

By editing [MCFPaxos.tla](MCFPaxos.tla), you can modify the configuration to test different models. For example, you might wish to try changing the number of acceptors, how quorums are composed or the number of ballots.

This specification is derived from Leslie Lamport's Paxos specification from [TLA+ Examples](https://github.com/tlaplus/Examples).
