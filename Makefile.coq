## Coq/Rocq Formalization Makefile

.PHONY: all coq clean-coq help

# Default target
all: coq

# Build all Coq files
coq:
	@echo "Building Coq formalization..."
	coq_makefile -f _CoqProject -o CoqMakefile
	$(MAKE) -f CoqMakefile

# Clean Coq build artifacts
clean-coq:
	@echo "Cleaning Coq build artifacts..."
	@if [ -f CoqMakefile ]; then $(MAKE) -f CoqMakefile clean; fi
	@rm -f CoqMakefile CoqMakefile.conf
	@find coq -name "*.vo" -o -name "*.vok" -o -name "*.vos" -o -name "*.glob" -o -name ".*.aux" | xargs rm -f

# Help target
help:
	@echo "Coq/Rocq Formalization Makefile"
	@echo "--------------------------------"
	@echo "Targets:"
	@echo "  all        - Build all Coq files (default)"
	@echo "  coq        - Build Coq formalization"
	@echo "  clean-coq  - Clean Coq build artifacts"
	@echo "  help       - Show this help message"
	@echo ""
	@echo "The formalization includes:"
	@echo "  - CollatzBasics.v    : Core definitions and main convergence theorem"
	@echo "  - CollatzRows.v      : Row operations and steering lemmas"
	@echo "  - CollatzLifting.v   : Residue lifting and reachability theorems"
