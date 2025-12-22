## Dockerfile for isar2html

FROM mcr.microsoft.com/dotnet/sdk:10.0

COPY isar2html2.0 /home/IsarMathLib/isar2html2.0

COPY IsarMathLib /home/IsarMathLib/IsarMathLib

WORKDIR /home/IsarMathLib/isar2html2.0

RUN dotnet build --configuration Release && ln -s src/isar2html/bin/Release/net10.0/isar2html iht

ENTRYPOINT ["./iht"]
