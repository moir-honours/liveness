<a id="readme-top"></a>

<!-- PROJECT TITLE -->
<br />
<div align="center">
  <h3 align="center">Mechanised verification of Lamport's bakery algorithm</h3>

  <p align="center">
    COSC 470
  </p>
</div>

<!-- ABOUT THE PROJECT -->

## About The Project

![Lean](https://img.shields.io/badge/lean_4-v4.28.0-%23000000.svg?style=for-the-badge)
![Veil](https://img.shields.io/badge/veil-39fb34d-%23654FF0.svg?style=for-the-badge)
![TLA+](https://img.shields.io/badge/TLA%2B-benchmark-%23007ACC.svg?style=for-the-badge)

Leslie Lamport's bakery algorithm is a foundational solution in concurrent programming. Concurrent algorithms are notoriously difficult to implement correctly, and recently there has been interest in formalising them. Model checking approaches for verifying correctness properties are only effective for a small, fixed number of processes. These are prone to state space explosion, and proofs for arbitrary finite _N_ are mostly informal, or in older tools. This project verifies mutual exclusion for the bakery algorithm using Lean 4 and Veil, building on Veil's model-checked bakery example. This project proves safety properties using manual proofs for critical section transitions, and SMT-checked invariants for other actions. The project proves progress of processes through the doorway without the use of SMT solvers, using the assumption of weak fairness on actions, and a ranking function for loops in states. Progress from waiting to the critical section, and therefore starvation freedom, is not yet mechanised.

<!-- GETTING STARTED -->

## Getting Started

### Prerequisites

To build this project, you'll need the Lean toolchain manager `elan` installed on your device. It installs the correct Lean version (`v4.28.0`, from `lean-toolchain`) automatically.

- <a href = "https://github.com/leanprover/elan"> elan</a>

### Installation

_Below are instructions for how you can clone and build the project._

1. Clone the repo with
   ```sh
   git clone https://github.com/moir-honours/liveness.git
   ```
2. Enter the project
   ```sh
   cd liveness
   ```
3. Fetch the dependencies (including Veil, pinned in `lakefile.toml`) and download the prebuilt Mathlib cache, so Mathlib doesn't have to be compiled from source
   ```sh
   lake exe cache get
   ```
4. Build the project
   ```sh
   lake build
   ```

<!-- CONTACT -->

## Contact

Max Moir - mmo199@uclive.ac.nz - maxwmoir@gmail.com

<p align="right">(<a href="#readme-top">back to top</a>)</p>
