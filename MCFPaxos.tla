-------------------------------- MODULE MCFPaxos -------------------------------
EXTENDS FPaxos, TLC
-----------------------------------------------------------------------------
CONSTANTS a1, a2, a3, a4  \* acceptors
CONSTANTS v1, v2      \* Values

MCAcceptor == {a1, a2, a3, a4}
MCValue    == {v1, v2}
MCQuorum1 == {{a1, a2},{a3, a4}}
MCQuorum2 == {{a1, a3},{a2, a4}}
MCBallot == 0..1

=============================================================================