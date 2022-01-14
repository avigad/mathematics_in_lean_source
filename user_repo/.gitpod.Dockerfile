FROM gitpod/workspace-full

RUN curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | sh -s -- --default-toolchain none --no-modify-path -y 
ENV PATH="$HOME/.elan/bin:${PATH}"
