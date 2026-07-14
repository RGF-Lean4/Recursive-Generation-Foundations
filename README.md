# Recursive Generation Foundations (RGF)

<div align="center">

**A formal framework for recursive generation methods in structured problem-solving**

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Language: Lean 4](https://img.shields.io/badge/Language-Lean%204-blue.svg)](https://lean-lang.org/)

[Overview](#overview) • [Getting Started](#quick-start) • [Key Concepts](#key-concepts) • [Architecture](#architecture) • [Contributing](#contributing)

</div>

---

## Overview

**Recursive Generation Foundations (RGF)** is a research and engineering initiative focused on the theory and practical implementation of **recursive generation methods** for structured content and decision-making. It provides a formal framework—implemented primarily in **Lean 4**—for decomposing complex generation tasks into smaller subproblems, solving them recursively, and composing results while maintaining correctness guarantees.

### Why RGF?

Many real-world generative systems benefit from structured decomposition:
- **Software synthesis** breaks down code generation into smaller AST components
- **Proof assistants** decompose theorem-proving into simpler subgoals
- **LLM-based reasoning** uses chain-of-thought to break down complex queries
- **Planning systems** recursively decompose goals into actionable steps

RGF abstracts and formalizes these patterns, providing:
- ✅ **Provable correctness** through formal verification in Lean 4
- ✅ **Modularity** via well-defined interfaces for generators and composition
- ✅ **Resource control** with bounded recursion, timeouts, and cost accounting
- ✅ **Reproducibility** with deterministic execution and comprehensive tracing

---

## Quick Start

### Prerequisites

- **Lean 4** (v4.0.0 or later)
- **Lake** (Lean package manager, included with Lean)

### Installation

1. Clone the repository:
```bash
git clone https://github.com/RGF-Lean4/Recursive-Generation-Foundations.git
cd Recursive-Generation-Foundations
```

2. Build the project:
```bash
lake build
```

3. Run tests:
```bash
lake test
```

### First Example

```lean
import RGF.Core
import RGF.Generators

-- Define a simple generation task
def exampleTask : Task := {
  goal := "generate a simple example",
  depth := 0,
  maxDepth := 10
}

-- Run the generator
#eval exampleTask |> basicGenerator
```

For more examples, see [examples/](./examples/) directory.

---

## Key Concepts

### 1. **Task**
A structured description of a generation goal.
```lean
structure Task where
  goal : String                    -- Primary objective
  metadata : Map String String     -- Additional context
  budget : Option ResourceBudget   -- Optional resource limits
  depth : Nat                      -- Current recursion depth
  maxDepth : Nat                   -- Maximum recursion depth
```

### 2. **Generator**
A composable object that accepts a Task and produces either:
- A **Result** (direct solution), or
- A set of **SubTasks** (problems to solve recursively)

```lean
structure Generator (α : Type) where
  name : String
  solve : Task → Except String (Result α | List Task)
```

### 3. **Result**
A typed payload produced by a generator, including:
- The computed value
- Success/failure markers
- Provenance and trace information
- Resource accounting

```lean
structure Result (α : Type) where
  value : α
  success : Bool
  trace : List String          -- Execution log
  resources : ResourceUsage    -- CPU, memory, calls
```

### 4. **Composition Operators**
Primitives to combine sub-results:
- **Sequential**: solve T1, then use result in T2
- **Parallel**: solve independent subtasks concurrently
- **Alternative**: try multiple generators, keep first success
- **Aggregate**: combine results from subtasks with a fold

### 5. **Verification Hooks**
Optional checks validating sub-results before composition:
```lean
structure Verifier (α : Type) where
  check : α → Except String Unit  -- Throws if invariant violated
```

### 6. **Scheduler**
Determines execution order of subtasks:
- Depth-first
- Breadth-first
- Priority-based
- Custom scheduling strategies

---

## Architecture

### Directory Structure

```
.
├── lakefile.toml              # Lake build configuration
├── README.md                  # This file
├── CONTRIBUTING.md            # Contribution guidelines
├── LICENSE                    # MIT License
│
├── RGF/
│   ├── Core/
│   │   ├── Task.lean          # Task definition and properties
│   │   ├── Result.lean        # Result type and composition
│   │   ├── Generator.lean     # Generator interface and combinators
│   │   ├── Scheduler.lean     # Task scheduling strategies
│   │   └── Verifier.lean      # Verification and validation
│   │
│   ├── Generators/
│   │   ├── Basic.lean         # Simple reference generators
│   │   ├── Tree.lean          # Tree-based decomposition
│   │   ├── DAG.lean           # DAG-based decomposition
│   │   └── Symbolic.lean      # Symbolic computation generators
│   │
│   ├── Composition/
│   │   ├── Sequential.lean    # Sequential composition
│   │   ├── Parallel.lean      # Parallel composition
│   │   ├── Alternative.lean   # Alternative/fallback composition
│   │   └── Aggregate.lean     # Result aggregation
│   │
│   ├── Resource/
│   │   ├── Budget.lean        # Resource budget definitions
│   │   ├── Accounting.lean    # Resource tracking
│   │   └── Limits.lean        # Enforcement of resource limits
│   │
│   ├── Verification/
│   │   ├── Invariants.lean    # Common invariant definitions
│   │   └── Tactics.lean       # Tactic library for proofs
│   │
│   └── Utils/
│       ├── Trace.lean         # Tracing and logging utilities
│       ├── Error.lean         # Error handling and reporting
│       └── Metrics.lean       # Performance metrics collection
│
├── tests/
│   ├── UnitTests/
│   │   ├── CoreTests.lean
│   │   ├── GeneratorTests.lean
│   │   └── CompositionTests.lean
│   │
│   └── IntegrationTests/
│       ├── EndToEndTests.lean
│       └── PerformanceTests.lean
│
├── examples/
│   ├── SimpleDecomposition.lean
│   ├── TreeGeneration.lean
│   ├── ProofSearch.lean
│   └── OptimizationProblem.lean
│
├── docs/
│   ├── ARCHITECTURE.md        # Detailed architecture document
│   ├── API_REFERENCE.md       # API documentation
│   ├── DESIGN_DECISIONS.md    # Design rationale and choices
│   ├── REPRODUCIBILITY.md     # Reproduction guide
│   └── research/
│       └── related_work.md    # Related work and references
│
└── scripts/
    ├── run_tests.sh
    ├── benchmark.sh
    └── generate_docs.sh
```

### Core Data Flow

```
┌─────────────────────────────────────────────────────────┐
│                    Input Task                           │
└──────────────────────┬──────────────────────────────────┘
                       │
                       ▼
         ┌─────────────────────────────┐
         │   Generator.solve(task)     │
         └──────────┬──────────────────┘
                    │
          ┌─────────┴──────────┐
          │                    │
          ▼                    ▼
      ┌────────────┐     ┌──────────────┐
      │ Direct     │     │ Sub-Tasks    │
      │ Result     │     │ Detected     │
      └────────────┘     └──────┬───────┘
          │                     │
          │             ┌───────▼────────┐
          │             │ Schedule &     │
          │             │ Execute        │
          │             │ Recursively    │
          │             └───────┬────────┘
          │                     │
          │             ┌───────▼────────┐
          │             │ Verify         │
          │             │ Sub-Results    │
          │             └───────┬────────┘
          │                     │
          └──────────┬──────────┘
                     │
                     ▼
          ┌──────────────────────┐
          │ Compose Results      │
          └──────────┬───────────┘
                     │
                     ▼
          ┌──────────────────────┐
          │ Final Result + Trace │
          │ + Resource Accounting│
          └──────────────────────┘
```

---

## Evaluation and Metrics

To assess an RGF implementation, track:

| Metric | Description | Target |
|--------|-------------|--------|
| **Correctness** | Fraction of tasks satisfying specification | >95% |
| **Efficiency** | Subcalls and wall-clock time per task | Baseline dependent |
| **Scalability** | Behavior as task complexity increases | Linear/logarithmic growth |
| **Robustness** | Graceful handling of partial failures | >99% recovery |
| **Reproducibility** | Deterministic results with same seeds | 100% |

Experiments **must** log:
- Generation traces (call stacks, decisions)
- Resource accounting (CPU, memory, API calls)
- Verification outcomes
- Timing breakdowns

---

## Usage Patterns

### Pattern 1: Simple Recursive Decomposition

```lean
def solveSimple (task : Task) : Result Int := by
  if task.depth ≥ task.maxDepth then
    return { value := 0, success := false, trace := ["Max depth exceeded"] }
  else
    let subTasks := decomposeTask task
    let results := subTasks.map (solveSimple · |> incrementDepth)
    return aggregateResults results
```

### Pattern 2: Generator Composition

```lean
def robustSolver : Generator Int :=
  (primaryGenerator <|> secondaryGenerator) >>=
  fun result => verifyAndCompose result
```

### Pattern 3: Resource-Bounded Recursion

```lean
def boundedSolve (task : Task) (budget : ResourceBudget) : Result Int :=
  if budget.remainingTime ≤ 0 then
    return timeoutResult
  else
    let result := solve task
    if result.resources.exceeded then
      return budgetExceededResult
    else
      return result
```

---

## Design Goals

- **Modularity**: Clear separation of concerns
  - Problem decomposition
  - Base-case solvers
  - Composition logic
  - Verification

- **Reproducibility**: 
  - Deterministic where feasible
  - Comprehensive logging
  - Seed management
  - Trace export

- **Extensibility**:
  - Pluggable generator backends
  - Custom schedulers
  - Extensible verifiers
  - Modular composition operators

- **Safety & Control**:
  - Recursion depth limits
  - Resource budgets (time, memory, calls)
  - Graceful failure handling
  - Partial result recovery

---

## Documentation

| Document | Purpose |
|----------|---------|
| [ARCHITECTURE.md](./docs/ARCHITECTURE.md) | Detailed design, invariants, and data flows |
| [API_REFERENCE.md](./docs/API_REFERENCE.md) | Complete API documentation |
| [DESIGN_DECISIONS.md](./docs/DESIGN_DECISIONS.md) | Rationale for key design choices |
| [REPRODUCIBILITY.md](./docs/REPRODUCIBILITY.md) | How to run experiments and reproduce results |
| [examples/](./examples/) | Annotated example use cases |

---

## Contributing

We welcome contributions! Please see [CONTRIBUTING.md](./CONTRIBUTING.md) for guidelines.

### Contribution Process

1. **Open an Issue** describing the feature or bug with:
   - Clear problem statement
   - Minimal reproducible example
   - Expected vs. actual behavior

2. **Submit a Pull Request** with:
   - Focused, well-documented commits
   - Tests for new functionality
   - Updated documentation
   - Clear PR description linking to the issue

3. **Code Standards**:
   - Follow Lean 4 naming conventions
   - Include docstrings for public APIs
   - Maintain >80% test coverage
   - Use semantic versioning for releases

### Areas Seeking Contributions

- [ ] Additional generator implementations
- [ ] Custom scheduler strategies
- [ ] Performance optimization
- [ ] Documentation and examples
- [ ] Experimental evaluation
- [ ] Integration with external tools

---

## Performance & Benchmarking

Performance measurements are in [docs/BENCHMARKS.md](./docs/BENCHMARKS.md).

To run benchmarks locally:
```bash
lake build
./scripts/benchmark.sh
```

---

## Related Work

RGF draws inspiration from:
- **Recursive descent parsing** and AST decomposition
- **Proof search** and tactic-based theorem proving
- **Program synthesis** (e.g., type-directed synthesis, oracle-guided induction)
- **Hierarchical planning** (HTN, STRIPS decomposition)
- **Compositional generalization** in machine learning

See [docs/research/related_work.md](./docs/research/related_work.md) for detailed references.

---

## License

This project is licensed under the **MIT License**—see [LICENSE](./LICENSE) for details.

---

## Citation

If you use RGF in published work, please cite:

```bibtex
@software{rgf2026,
  title = {Recursive Generation Foundations: A Formal Framework for Recursive Generation},
  author = {RGF-Lean4},
  url = {https://github.com/RGF-Lean4/Recursive-Generation-Foundations},
  year = {2026}
}
```

---

## Contact & Support

- **Issues & Discussions**: Use [GitHub Issues](https://github.com/RGF-Lean4/Recursive-Generation-Foundations/issues)
- **Questions**: Open a Discussion or check existing issues
- **Security**: Please report security vulnerabilities responsibly to maintainers

---

## Status & Roadmap

**Current Status**: Early research/development phase

### Roadmap

- [x] Core abstractions (Task, Generator, Result)
- [x] Basic composition operators
- [x] Resource accounting framework
- [ ] Advanced schedulers (priority-based, adaptive)
- [ ] Integration with proof assistants
- [ ] Performance benchmarking suite
- [ ] Experimental evaluation on benchmark tasks
- [ ] Community feedback & refinement

---

**Last Updated**: July 2026  
**Maintainers**: RGF-Lean4 Team

