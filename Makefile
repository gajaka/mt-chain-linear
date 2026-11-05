.PHONY: check core framework

# Two proof layers in one repository. The original Theta(n) import closure
# remains unchanged; the full generic framework is an additional local build.
check: core framework

core:
	lake build

framework:
	python3 framework/check.py
