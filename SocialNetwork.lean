/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.Appendix
import SocialNetwork.Band
import SocialNetwork.BandCollapse
import SocialNetwork.Bias
import SocialNetwork.BiasedConcentration
import SocialNetwork.BiasedConsensusExit
import SocialNetwork.BiasedExistence
import SocialNetwork.BiasedExitTime
import SocialNetwork.BiasedHitting
import SocialNetwork.BiasedMetastability
import SocialNetwork.BiasedModel
import SocialNetwork.BiasedNonExplosion
import SocialNetwork.BiasedResults
import SocialNetwork.BiasedTransfer
import SocialNetwork.Clocks
import SocialNetwork.Concentration
import SocialNetwork.Consensus
import SocialNetwork.ConsensusExit
import SocialNetwork.ContinuousTime
import SocialNetwork.Defs
import SocialNetwork.Doeblin
import SocialNetwork.Examples
import SocialNetwork.Existence
import SocialNetwork.ExitTime
import SocialNetwork.Favouring
import SocialNetwork.Frequencies
import SocialNetwork.Graphical
import SocialNetwork.Greedy
import SocialNetwork.JumpHold
import SocialNetwork.Kac
import SocialNetwork.Ladder
import SocialNetwork.MainResults
import SocialNetwork.Markov
import SocialNetwork.Metastability
import SocialNetwork.Minorisation
import SocialNetwork.NonExplosion
import SocialNetwork.Skeleton
import SocialNetwork.Trajectory
import SocialNetwork.Transfer

/-!
# Formalisation of arXiv:2607.19651

*Metastability and phase transition in a social network model with multiple opinions*,
Felipe Penafiel and Kádmo Laxa.

`SocialNetwork.MainResults` restates the main theorems of the paper in one place.  The
blueprint (`blueprint/src/content.tex`) gives the Lean counterpart of every numbered statement,
and `STATUS.md` the status of each.
-/
