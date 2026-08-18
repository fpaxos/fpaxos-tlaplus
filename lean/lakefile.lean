import Lake
open Lake DSL

package fpaxos where

require Veil from git
  "https://github.com/verse-lab/veil.git" @
  "300c305e945750ab3fb62de4a79c23161b24da39"

@[default_target]
lean_lib FPaxos where
  roots := #[`FPaxos, `FPaxosProof]
