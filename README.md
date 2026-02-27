# Coq / Rocq Dependency Analyzer & Visualizer

Working on a large Coq (or Rocq) project?

Understanding proof dependencies, admitted lemmas, and trust chains becomes painful as your codebase grows. This tool parses your `.v` files, builds a full dependency graph, and generates an interactive web interface for exploring your project structure.

It's designed for real proof engineering work; not just pretty graphs.

---

## Screenshots

<table align="center">
  <tr>
    <td align="center">
      <img src="https://raw.githubusercontent.com/SaxonRah/Coq-Dependency-Analyzer/main/Coq_Dependencies.png"
           alt="Analyzer"
           width="500"><br>
      <b>Analyzer View</b>
    </td>
    <td align="center">
      <img src="https://raw.githubusercontent.com/SaxonRah/Coq-Dependency-Analyzer/main/Coq_Graph.png"
           alt="Visualizer"
           width="500"><br>
      <b>Graph Visualizer</b>
    </td>
  </tr>
</table>

---

## What It Does

The **Analyzer**:

* Parses Coq/Rocq `.v` files
* Extracts definitions, theorems, lemmas, axioms, parameters
* Builds a full dependency graph
* Tracks admitted and axiom taint propagation
* Outputs:

  * Interactive HTML report
  * JSON graph for external tools

The **Visualizer**:

* Loads the JSON graph
* Renders a high-performance interactive dependency graph
* Designed to scale to large Coq projects

---

## Why This Is Useful

### :godmode: Taint Propagation (Most Important Feature)

Every `Admitted` and `Axiom` is treated as a source of logical uncertainty.

The analyzer:

* Propagates dependency taint forward
* Marks any theorem that *transitively* depends on admitted/axiom content
* Shows you which "proved" results actually rest on unfinished work

This is essential for:

* Auditing formal verification projects
* Managing proof debt
* Preparing code for publication or review

---

## Features

### Dependency Exploration

* Click any definition/theorem to see:

  * Its direct dependencies
  * Its full transitive dependency tree
* Reverse dependency view:

  * "What breaks if I change this?"

### Status Tracking

Color coding:

* 🟢 Green : fully proved
* 🟡 Yellow : admitted
* 🔵 Blue : definition
* 🟣 Purple : axiom / parameter
* 🔴 Red : depends on admitted / tainted

### Proof Debt Dashboard

* Counts of admitted lemmas
* Axiom usage
* Tainted theorem statistics

### Code Health

* Unused definition detection
* Trust chain auditing

### Data Export

* JSON output for:

  * Gephi
  * Custom scripts
  * Further analysis pipelines

---

## Usage

### Analyzer

```bash
python coq_analyzer.py /path/to/coq/project [-o output.html] [--json]
```

Options:

* `-o output.html` : custom HTML output file
* `--json` : export dependency graph as JSON (required for visualizer)

---

### Visualizer

Run the analyzer first to generate JSON.

```bash
python coq_visualizer.py /path/to/analyzer_output.json --open
```

* Loads the JSON graph
* Opens interactive dependency graph in browser

The visualizer is optimized for performance on large projects, but layout mechanics (spreading/relaxing nodes) are still evolving.

---

## Project Structure

* `coq_analyzer.py` : Main `.v` file analyzer (stable)
* `coq_visualizer.py` : Interactive graph renderer
* `coq_glob_analyzer.py` : Experimental `.glob` analyzer (currently broken)

  * Instructions are included near `__main__`
  * Not actively maintained

---

## When To Use This

This tool is especially helpful if:

* Your project has hundreds or thousands of lemmas
* You're unsure how deeply an admitted proof infects the rest of the development
* You want to understand the blast radius of changing a foundational lemma
* You need an audit trail before publishing or freezing a development
* You want to export structural data for complexity or graph analysis

---

## Philosophy

Large proof developments become opaque over time.

This tool makes them inspectable.

It treats a Coq project like a dependency system; not just a collection of files; and exposes:

* Structural fragility
* Logical trust chains
* Hidden proof debt

If you care about the integrity of your formal system, you need this visibility.
