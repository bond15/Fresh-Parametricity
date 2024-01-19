FROM haskell:9.2.6

USER root
RUN apt-get update
RUN apt-get install -y cabal-install

RUN cabal update
RUN cabal install alex
RUN cabal install happy
RUN cabal install Agda-2.6.4

RUN git clone https://github.com/agda/agda-stdlib --branch v2.0
RUN git clone https://github.com/agda/cubical.git --branch v0.6
RUN apt-get install -y emacs

WORKDIR /root/
RUN mkdir /root/.agda
RUN echo "/agda-stdlib/standard-library.agda-lib" >> /root/.agda/libraries
RUN echo "/cubical/cubical.agda-lib" >> /root/.agda/libraries

ENTRYPOINT ["tail", "-f", "/dev/null"]