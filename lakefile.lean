import Lake
open Lake DSL

package «TorusVelocityTether»

require TorusFourierNS from git
  "https://github.com/BenFrohman/torus-fourier-ns-lemmas.git" @ "a2c4d0e22cf7f8f637c5b4e7f0287b9da45ea189"

@[default_target]
lean_lib «TorusVelocityTether» where
  roots := #[`TorusVelocityTether]
