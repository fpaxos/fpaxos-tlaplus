---- MODULE MCFPaxosThreeAcc ----

EXTENDS FPaxos, TLC

MCAcceptor == {"a1", "a2", "a3"}
MCValue    == 0..2
MCQuorum1 == {{"a1", "a2"}, {"a1", "a3"}, {"a2", "a3"}}
MCQuorum2 == {{"a1", "a2"}, {"a1", "a3"}, {"a2", "a3"}}
MCBallot == 0..2

====