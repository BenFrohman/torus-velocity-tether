import Lake
open Lake DSL

package «TorusVelocityTether»

require TorusFourierNS from git
  "https://github.com/BenFrohman/torus-fourier-ns-lemmas.git" @ "66c3d7ae9dc81363e07c488edb0e373e2c689697"

@[default_target]
lean_lib «TorusVelocityTether» where
  roots := #[`TorusVelocityTether]
