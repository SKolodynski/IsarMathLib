## Dockerfile for IsarMathLib

FROM isabelle-zf-2022

COPY IsarMathLib /home/isabelle/IsarMathLib

USER root
RUN chown isabelle /home/isabelle/IsarMathLib
USER isabelle

CMD ["build", "-D", "/home/isabelle/IsarMathLib"]

