---- MODULE MCFPaxosTwoAcc ----

EXTENDS FPaxos, TLC

MCAcceptor == {"a1", "a2"}
MCValue    == {0, 1}
MCQuorum1 == {{"a1"}, {"a2"}}
MCQuorum2 == {{"a1", "a2"}}
MCBallot == 0..2

====