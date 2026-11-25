# Toolchain for the verified Pancake quicksort:
#   Poly/ML 5.9.2  ->  HOL4 (trindemossen-2-v10)  ->  CakeML v3671 sources + bootstrapped compiler
# The HOL and CakeML commits are the pair the CakeML v3671 release was built and tested with.
FROM ubuntu:24.04

ARG POLY_VERSION=5.9.2
ARG HOL_COMMIT=9783a49979c94c401ff8c0e51b2eefae7ea95ae3
ARG CAKEML_COMMIT=16bdb1aaaab64a6ac66504ad2e9f0ed6146060e9
ARG CAKEML_RELEASE=v3671

ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
      build-essential git curl ca-certificates libgmp-dev python3 time \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /opt

# ---- Poly/ML ----
RUN curl -sL https://github.com/polyml/polyml/archive/refs/tags/v${POLY_VERSION}.tar.gz | tar xz \
 && cd polyml-${POLY_VERSION} \
 && ./configure --prefix=/usr/local --enable-shared \
 && make -j"$(nproc)" && make install && ldconfig \
 && cd /opt && rm -rf polyml-${POLY_VERSION}

# ---- HOL4 ----
RUN git clone https://github.com/HOL-Theorem-Prover/HOL.git \
 && cd HOL && git checkout ${HOL_COMMIT} \
 && poly < tools/smart-configure.sml \
 && bin/build
ENV HOLDIR=/opt/HOL
ENV PATH=/opt/HOL/bin:$PATH

# ---- CakeML sources (for the Pancake semantics/parser theories) ----
RUN git clone https://github.com/CakeML/cakeml.git \
 && cd cakeml && git checkout ${CAKEML_COMMIT}
ENV CAKEMLDIR=/opt/cakeml

# ---- Bootstrapped, verified CakeML compiler binary (supports --pancake) ----
RUN mkdir -p /opt/cake && cd /opt/cake \
 && curl -sL https://github.com/CakeML/cakeml/releases/download/${CAKEML_RELEASE}/cake-x64-64.tar.gz | tar xz \
 && cd cake-x64-64 && make cake
ENV PATH=/opt/cake/cake-x64-64:$PATH
