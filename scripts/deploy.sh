#!/usr/bin/env bash
set -e
if [ "$#" -ne 2 ]; then
    echo "Usage example: $0 leanprover-community mathematics_in_lean"
    exit 1
fi

# Build
make clean html latexpdf

# 3. Deploy
rm -rf deploy
git clone git@github.com:$1/$2 deploy
cd deploy
rm -rf * .gitignore
cp -Lr ../user_repo/./ .
git add .
git add -f .vscode
git commit -m "Update `date`"
git push

git checkout gh-pages
rm -rf * .gitignore .buildinfo .nojekyll
cp -r ../build/html/./ .
cp ../build/latex/mathematics_in_lean.pdf .
touch .nojekyll
git add .
git commit -m "Update `date`"
git push

cd ..
rm -rf deploy
