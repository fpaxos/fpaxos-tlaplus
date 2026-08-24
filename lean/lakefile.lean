import Lake
open Lake DSL

package fpaxos where

@[default_target]
lean_lib FPaxos where
  roots := #[`FPaxos, `Fpaxos, `Proof]
