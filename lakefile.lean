import Lake
open Lake DSL

package «TorusVelocityTether»

require TorusFourierNS from git
  "https://github.com/BenFrohman/torus-fourier-ns-lemmas.git" @ "a241bf427d25be13e358c6df09176ca3f3ad75e4"

@[default_target]
lean_lib «TorusVelocityTether» where
  roots := #[`TorusVelocityTether]
