---- MODULE MCFPaxosFourAccLarge ----

EXTENDS FPaxos, TLC

MCAcceptor == {"a1", "a2", "a3", "a4"}
MCValue    == 0..10
MCQuorum1 == {{"a1", "a2"}, {"a3", "a4"}}
MCQuorum2 == {{"a1", "a3"}, {"a2", "a4"}}
MCBallot == 0..10

====