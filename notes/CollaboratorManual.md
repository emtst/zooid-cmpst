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
