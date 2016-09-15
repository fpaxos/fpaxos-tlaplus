
This repository contains the [TLA+](research.microsoft.com/en-us/um/people/lamport/tla/tla.html) specification and model checking setup for single valued F-Paxos.

You can check this specification by installing [TLA+](http://research.microsoft.com/en-us/um/people/lamport/tla/tla.html) and clone this directory:
```
java -cp <path-to-tla> tlc2.TLC MCFPaxos.tla
```

By editing [MCFPaxos.tla](MCFPaxos.tla), you can modify the configuration to test different models. For example, you might wish to try changing the number of acceptors, how quorums are composed and the number of ballots.

This specification is derived from Lamport's Paxos specification from [TLA+ Examples](https://github.com/tlaplus/Examples).
