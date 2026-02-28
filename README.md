# 🛡️ A Verified Constructive Reduction of the Cook-Levin Theorem in Lean 4

[![Lean 4](https://img.shields.io/badge/Language-Lean%204-blue.svg)](https://leanprover.github.io/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

> **Bridging the Gap Between Complexity Theory and Formal SAT Encodings**

## 📖 Overview

This repository contains the complete, machine-checked formalization of the **Cook-Levin Theorem** in **Lean 4**.

While the Cook-Levin theorem is fundamental to computational complexity, formalizations in proof assistants often rely on high-level arguments rather than constructing the concrete Satisfiability (SAT) formula. This project addresses this gap by providing a **rigorous, constructive reduction** from a deterministic Turing Machine model to a Conjunctive Normal Form (CNF) formula.

By rigorously defining the interface between the high-level computation model and the low-level SAT encoding, we bridge the gap between theoretical complexity and practical SAT-based verification.

## 🏗️ Technical Highlights

Our work specifically handles the following challenges in a verified setting:

* **Verified 3D-Variable Indexing**: Mapping a Turing machine computation grid (Time $\times$ Position $\times$ Symbol/State) to a 1D linear SAT variable space.
* **Constructive CNF Generation**: Concrete, executable functions to generate clauses enforcing valid execution.
* **Total Soundness Proofs**: Mathematical guarantees that a satisfying assignment for the SAT formula corresponds to a valid, accepting Turing machine computation trace.

### The Mapping Process

The core of our reduction lies in mapping the 3D computation grid to a 1D linear variable space.


```lean
def get_var (params: MachineParams) (T t i s: Nat) : Nat :=
  (s + 1 + params.alphabet_size * (1 + params.state_count) * i + (T * params.alphabet_size * (1 + params.state_count) * t)) + 1
```

*(Simplified view of `get_var` function)*

## 📂 Repository Structure

* `Cook_Levine_Lean4.lean`: The core formalization of the reduction and soundness proofs.
* `Mathlib/`: Necessary dependencies (Lean 4 toolchain v4.28.0).

## 🛠️ Usage & Verification

This project is built and verified using Lean 4. To check the proofs, ensure you have Lean 4 installed and run:

```bash
lake build
```

## 📝 License

This project is licensed under the MIT License - see the LICENSE file for details.
