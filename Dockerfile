## Dockerfile for IsarMathLib

FROM slawekkol/isarmathlib:isabelle-zf-2025-1

COPY IsarMathLib /home/isabelle/IsarMathLib

USER root
RUN chown -R isabelle:isabelle /home/isabelle/IsarMathLib
USER isabelle

CMD ["build","-o","show_results=false","-D", "/home/isabelle/IsarMathLib"]


