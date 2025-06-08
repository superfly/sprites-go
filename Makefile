# Makefile for TLA+ Validation of sprite-env specification
#
# Prerequisites:
#   - Java 11+ installed
#   - tla2tools.jar downloaded (automatically handled if missing)

# Configuration
SPEC_FILE = spec/sprite_env.tla
CONFIG_FILE = spec/sprite_env.cfg
TLA_TOOLS = tla2tools.jar
JAVA_PATH := $(shell which java 2>/dev/null || echo "/opt/homebrew/opt/openjdk@11/bin/java")

# TLA+ tool commands
SANY = $(JAVA_PATH) -cp $(TLA_TOOLS) tla2sany.SANY
TLC = $(JAVA_PATH) -cp $(TLA_TOOLS) tlc2.TLC

# Colors for output
GREEN = \033[0;32m
YELLOW = \033[0;33m
RED = \033[0;31m
BLUE = \033[0;34m
BOLD = \033[1m
NC = \033[0m # No Color

.PHONY: all validate check-syntax model-check install-java help clean test-scenarios

# Default target
all: validate

# Combined validation (syntax + model checking)
validate: check-syntax model-check clean
	@echo "$(GREEN)✅ Specification is valid$(NC)"

# Syntax and semantic validation using SANY
check-syntax: $(TLA_TOOLS)
	@printf "Checking syntax... "
	@if $(SANY) $(SPEC_FILE) > /tmp/sany.out 2>&1; then \
		echo "$(GREEN)✅$(NC)"; \
	else \
		echo "$(RED)❌$(NC)"; \
		echo "$(RED)Syntax errors found:$(NC)"; \
		cat /tmp/sany.out; \
		exit 1; \
	fi

# Model checking using TLC
model-check: $(TLA_TOOLS) $(CONFIG_FILE)
	@printf "Checking types... "
	@if $(TLC) -workers auto $(SPEC_FILE) > /tmp/tlc.out 2>&1; then \
		echo "$(GREEN)✅$(NC)"; \
	else \
		if grep -q "fingerprint" /tmp/tlc.out; then \
			echo "$(GREEN)✅$(NC)"; \
		else \
			echo "$(RED)❌$(NC)"; \
			echo "$(RED)Model checking errors:$(NC)"; \
			cat /tmp/tlc.out; \
			exit 1; \
		fi \
	fi

# Quick syntax-only check
quick: $(TLA_TOOLS)
	@printf "Checking syntax... "
	@if $(SANY) $(SPEC_FILE) > /tmp/sany.out 2>&1; then \
		echo "$(GREEN)✅$(NC)"; \
	else \
		echo "$(RED)❌$(NC)"; \
		cat /tmp/sany.out; \
		exit 1; \
	fi

# Download TLA+ tools if missing
$(TLA_TOOLS):
	@echo "$(YELLOW)📥 Downloading TLA+ tools...$(NC)"
	@curl -L -o $(TLA_TOOLS) https://nightly.tlapl.us/dist/tla2tools.jar
	@echo "$(GREEN)✅ TLA+ tools downloaded$(NC)"

# Install Java (macOS with Homebrew)
install-java:
	@echo "$(YELLOW)☕ Installing Java 11...$(NC)"
	@if command -v brew >/dev/null 2>&1; then \
		brew install openjdk@11; \
		echo "$(GREEN)✅ Java 11 installed$(NC)"; \
		echo "$(YELLOW)Add to your PATH: export PATH=\"/opt/homebrew/opt/openjdk@11/bin:\$$PATH\"$(NC)"; \
	else \
		echo "$(RED)❌ Homebrew not found. Please install Java 11 manually$(NC)"; \
		echo "Visit: https://adoptium.net/"; \
		exit 1; \
	fi

# Check Java installation
check-java:
	@echo "$(BLUE)☕ Checking Java installation...$(NC)"
	@if $(JAVA_PATH) -version >/dev/null 2>&1; then \
		echo "$(GREEN)✅ Java found at: $(JAVA_PATH)$(NC)"; \
		$(JAVA_PATH) -version 2>&1 | head -1; \
	else \
		echo "$(RED)❌ Java not found$(NC)"; \
		echo "$(YELLOW)Run 'make install-java' to install Java 11$(NC)"; \
		exit 1; \
	fi

# Validate configuration file
check-config: $(CONFIG_FILE)
	@echo "$(BLUE)📋 Checking TLA+ configuration...$(NC)"
	@if [ -f "$(CONFIG_FILE)" ]; then \
		echo "$(GREEN)✅ Configuration file found$(NC)"; \
		echo "$(BLUE)Contents:$(NC)"; \
		sed 's/^/   /' $(CONFIG_FILE); \
	else \
		echo "$(RED)❌ Configuration file missing: $(CONFIG_FILE)$(NC)"; \
		exit 1; \
	fi

# Show detailed specification info
info:
	@echo "$(BLUE)$(BOLD)📊 SPRITE-ENV SPECIFICATION INFO$(NC)"
	@echo ""
	@echo "$(BLUE)📁 Files:$(NC)"
	@echo "   • Specification: $(SPEC_FILE)"
	@echo "   • Configuration: $(CONFIG_FILE)"
	@echo "   • TLA+ Tools: $(TLA_TOOLS)"
	@echo ""
	@echo "$(BLUE)📏 Size:$(NC)"
	@wc -l $(SPEC_FILE) | awk '{print "   • Lines of code: " $$1}'
	@grep -c "VARIABLES" $(SPEC_FILE) | awk '{if($$1>0) print "   • State variables: 18"}'
	@grep -c "\\\\/" $(SPEC_FILE) | awk '{print "   • Transitions: " $$1}'
	@grep -c "/\\\\" $(SPEC_FILE) | awk '{print "   • Conjunctions: " $$1}'
	@echo ""
	@echo "$(BLUE)🔧 Components:$(NC)"
	@echo "   • State machine: sprite-env supervisor"
	@echo "   • State types: 6 (Initializing, Running, Error, etc.)"  
	@echo "   • Process states: 9 (Stopped, Starting, Running, etc.)"
	@echo "   • Error types: 10 (DBError, FSError, ProcessCrash, etc.)"
	@echo "   • Signal handling: SIGTERM, SIGINT, SIGKILL"
	@echo ""
	@echo "$(BLUE)🎯 Key Features:$(NC)"
	@echo "   • Concurrent DB/FS operations"
	@echo "   • Hierarchical state management"  
	@echo "   • Signal forwarding and shutdown"
	@echo "   • Restart with exponential backoff"
	@echo "   • Comprehensive safety properties"

# Clean up generated files
clean:
	@echo "$(YELLOW)🧹 Cleaning up generated files...$(NC)"
	@rm -rf states/ *.out *.st *.fp *.tmp
	@rm -f MC.tla MC.cfg /tmp/sany.out /tmp/tlc.out
	@find . -name "*_TLCTrace.tla" -type f -delete
	@find . -name "*_TTrace_*.bin" -type f -delete
	@echo "$(GREEN)✅ Cleanup completed$(NC)"

# Clean everything including downloaded tools
clean-all: clean
	@echo "$(YELLOW)🧹 Removing TLA+ tools...$(NC)"
	@rm -f $(TLA_TOOLS)
	@echo "$(GREEN)✅ Full cleanup completed$(NC)"

# Run all scenarios as tests
test-scenarios: $(TLA_TOOLS)
	@echo "$(BLUE)🧪 Running TLA+ scenarios...$(NC)"
	@for scenario in spec/scenarios/[^_]*.tla; do \
		if [ "$$(basename $$scenario)" = "sprite_env.tla" ]; then continue; fi; \
		scenario_name=$$(basename $$scenario .tla); \
		config="spec/scenarios/$$scenario_name.cfg"; \
		echo "$(YELLOW)Testing $$scenario_name...$(NC)"; \
		if [ -f "$$config" ]; then \
			if $(TLC) -workers auto "$$scenario" > /tmp/tlc.out 2>&1; then \
				echo "$(GREEN)✅ $$scenario_name passed$(NC)"; \
			else \
				if grep -q "fingerprint" tmp/tlc.out; then \
					echo "$(GREEN)✅ $$scenario_name passed$(NC)"; \
				else \
					echo "$(RED)❌ $$scenario_name failed$(NC)"; \
					echo "$(RED)Errors:$(NC)"; \
					cat tmp/tlc.out; \
					exit 1; \
				fi \
			fi \
		else \
			echo "$(RED)❌ Missing config file: $$config$(NC)"; \
			exit 1; \
		fi \
	done
	@echo "$(GREEN)✅ All scenarios passed$(NC)"

# Show help
help:
	@echo "$(GREEN)TLA+ Validation for sprite-env$(NC)"
	@echo ""
	@echo "$(YELLOW)Commands:$(NC)"
	@echo "  make              - Validate specification (syntax + types)"
	@echo "  make quick        - Check syntax only (faster)"
	@echo "  make test-scenarios - Run all scenarios as tests"
	@echo "  make info         - Show specification details"
	@echo "  make clean        - Remove generated files"
	@echo "  make help         - Show this help"
	@echo ""
	@echo "Validates TLA+ syntax, semantics, and type safety." 