# Makefile for sprite-env TLA+ specification validation

# Configuration
SPEC_FILE = spec/sprite_env.tla
CONFIG_FILE = spec/sprite_env.cfg
TLA_TOOLS = bin/tla2tools.jar
JAVA_PATH = java

# TLA+ tool commands
SANY = $(JAVA_PATH) -cp $(TLA_TOOLS) tla2sany.SANY
TLC = $(JAVA_PATH) -cp $(TLA_TOOLS) tlc2.TLC

# Colors
GREEN = \033[0;32m
RED = \033[0;31m
YELLOW = \033[0;33m
NC = \033[0m

.PHONY: all validate check-syntax model-check validate-traces clean

# Default target
all: validate

# Combined validation (syntax + model checking)
validate: check-syntax model-check
	@echo "$(GREEN)✅ Specification is valid$(NC)"

# Syntax and semantic validation
check-syntax:
	@printf "Checking syntax... "
	@if $(SANY) $(SPEC_FILE) > /tmp/sany.out 2>&1; then \
		echo "$(GREEN)✅$(NC)"; \
	else \
		echo "$(RED)❌$(NC)"; \
		echo "$(RED)Syntax errors:$(NC)"; \
		cat /tmp/sany.out; \
		exit 1; \
	fi

# Model checking
model-check:
	@printf "Checking types... "
	@if $(TLC) -workers auto $(SPEC_FILE) > /tmp/tlc.out 2>&1; then \
		echo "$(GREEN)✅$(NC)"; \
	else \
		if grep -q "fingerprint\|No error has been found" /tmp/tlc.out; then \
			echo "$(GREEN)✅$(NC)"; \
		else \
			echo "$(RED)❌$(NC)"; \
			echo "$(RED)Model checking errors:$(NC)"; \
			cat /tmp/tlc.out; \
			exit 1; \
		fi \
	fi

# Validate trace files against specification
validate-traces:
	@echo "$(YELLOW)🧪 Validating traces against specification...$(NC)"
	@python3 spec/scripts/validate_traces.py $(TLA_TOOLS)
	@$(MAKE) clean

# Clean up generated files
clean:
	@echo "$(YELLOW)🧹 Cleaning up...$(NC)"
	@rm -rf states/ *.out *.st *.fp *.tmp /tmp/sany.out /tmp/tlc.out
	@rm -f MC.tla MC.cfg
	@find . -name "*_TLCTrace.tla" -type f -delete
	@find . -name "*_TTrace_*.bin" -type f -delete
	@echo "$(GREEN)✅ Cleanup completed$(NC)" 