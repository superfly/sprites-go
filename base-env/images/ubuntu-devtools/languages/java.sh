#!/bin/bash
set -e
source /opt/asdf/asdf.sh

echo "=========================================="
echo "Installing and testing Java..."
echo "=========================================="

echo "Adding Java plugin..."
asdf plugin-add java https://github.com/halcyon/asdf-java.git
echo "Installing Java (OpenJDK 17)..."
asdf install java openjdk-17
echo "Setting Java global..."
asdf global java openjdk-17
echo "Testing Java..."
echo 'public class Hello { public static void main(String[] args) { System.out.println("hello"); } }' > /tmp/Hello.java
javac /tmp/Hello.java
java -cp /tmp Hello
rm /tmp/Hello.java /tmp/Hello.class

echo "✅ Java installed and tested successfully!" 