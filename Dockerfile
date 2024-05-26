## Dockerfile for IsarMathLib

FROM slawekkol/isarmathlib:isabelle-zf-2024

COPY IsarMathLib /home/isabelle/IsarMathLib

USER root
RUN chown -R isabelle:isabelle /home/isabelle/IsarMathLib
USER isabelle

CMD ["build", "-D", "/home/isabelle/IsarMathLib"]


