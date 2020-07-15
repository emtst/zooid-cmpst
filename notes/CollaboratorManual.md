# Collaborator Manual

## Setting up git merges

To have a clean commit history, we want to avoid merge commits. For that, we want to use rebase instead of merge.

Configure git to do this. Note that ```--global``` will do it for all your repos, omit it and run it in this repo and it will only affect this project.
```
git config --global branch.setuprebase always
```

You may also want:
```
git config --global rebase.autoStash true
git config --global pull.rebase true
```

## Working on features

Pushing to master is disabled, so instead we work on a branch and then create a pull request. Every commit will be compiled in the continous integration server and only branches that pass the test will be merged. For now, the test is just making the repository.
