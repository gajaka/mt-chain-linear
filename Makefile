.PHONY: check core certificates windows biased provenance barrier

# Focused mathematical package. No generic PPGraph or external case studies.
check: certificates windows biased provenance barrier

core:
	lake --wfail build

certificates: core
	cd research/certificate-existence && lake --wfail build CertificateStudy

windows:
	@set -e; for certificate in research/window-locality/evidence/*/CERTIFICATE.json; do \
		python3 -B research/window-locality/scripts/verify_certificate.py "$$certificate"; \
	done
	PYTHONOPTIMIZE=0 python3 -B research/window-locality/theory/homogeneous-width2/verify_raw_dual.py research/window-locality/theory/homogeneous-width2/DUAL_EXACT.json

biased: core
	cd research/biased-resampling && lake --wfail build BiasedResampling

provenance:
	python3 -B -c "import sys; sys.path.insert(0, 'scripts'); from provenance import validate_sources; print(validate_sources()['receipt'])"
	python3 -B research/certificate-existence/scripts/verify_sources.py

barrier:
	python3 -B experiments/barrier-guided-bias/verify.py
