# Coq-Dependency-Analyzer
Are you building a large Coq/Rocq Project? Need to visualize a dependency graph of your files interactively?

Coq-Dependency-Analyzer parses .v files from a Coq/Rocq project, builds a full dependency graph, and generates an interactive HTML page.

## Usage:
    python coq_analyzer.py /path/to/coq/project [-o output.html] [--json]
    
## Features
  - Clickable dependency trees for every theorem/lemma/definition
  - Reverse dependency view ("what breaks if I change this?")
  - Admitted/axiom audit trail (trust chain)
  - Proof debt dashboard with stats
  - Unused definition detection
  - Search and filter by kind, status, file
  - Color coding:
       - green : proved
       - yellow : admitted
       - blue : definition
       - purple : axiom/parameter
       - red : depends-on-admitted
  - JSON export

## Screenshot of WebPage
![Coq Dependencies Webpage](https://github.com/SaxonRah/Coq-Dependency-Analyzer/blob/main/Coq_Dependencies.png "Coq Dependencies Webpage")

## Reasons to use
The taint propagation is the most useful part for a real project. It traces transitively from every Admitted and Axiom forward through the dependency graph, so you can immediately see which "proven" theorems actually rest on unfinished work.

Other reasons include:
- The reverse dependency view answers "what's the blast radius if this admitted lemma turns out false?"
- The unused detection helps find dead code.
- The JSON export lets you pipe the data into Gephi or custom scripts for deeper analysis.
