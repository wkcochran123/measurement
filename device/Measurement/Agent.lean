/-
Measurement.Agent

Aggregator for the fast standalone Agent reimplementation. Imports only the
Agent subtree. This file is NOT imported by the root `Measurement.lean`; it
exists for direct checking of the Agent subtree in one command. The
root-import gate stays closed until the operator opens it.
-/
import Measurement.Agent.Core
import Measurement.Agent.Gates
import Measurement.Agent.Processes
import Measurement.Agent.Truth
