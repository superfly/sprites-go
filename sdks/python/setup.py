"""
Setup script for the Sprites Python SDK
"""

from setuptools import setup, find_packages
import os

# Read the README file
def read_readme():
    readme_path = os.path.join(os.path.dirname(__file__), 'README.md')
    if os.path.exists(readme_path):
        with open(readme_path, 'r', encoding='utf-8') as f:
            return f.read()
    return ''

setup(
    name='sprites-sdk',
    version='0.2.0',
    author='Sprites Team',
    author_email='support@sprites.dev',
    description='Python SDK for interacting with Sprites environments',
    long_description=read_readme(),
    long_description_content_type='text/markdown',
    url='https://github.com/sprite-env/python-sdk',
    packages=find_packages(),
    classifiers=[
        'Development Status :: 3 - Alpha',
        'Intended Audience :: Developers',
        'License :: OSI Approved :: MIT License',
        'Programming Language :: Python :: 3',
        'Programming Language :: Python :: 3.7',
        'Programming Language :: Python :: 3.8',
        'Programming Language :: Python :: 3.9',
        'Programming Language :: Python :: 3.10',
        'Programming Language :: Python :: 3.11',
        'Operating System :: OS Independent',
    ],
    python_requires='>=3.7',
    install_requires=[
        'websocket-client>=1.0.0',
        'requests>=2.25.0',
    ],
    extras_require={
        'test': [
            'pytest>=6.0.0',
            'pytest-cov>=2.10.0',
            'pytest-timeout>=1.4.0',
            'pytest-mock>=3.0.0',
        ],
        'dev': [
            'pytest>=6.0.0',
            'pytest-cov>=2.10.0',
            'pytest-timeout>=1.4.0',
            'pytest-mock>=3.0.0',
            'black>=22.0.0',
            'flake8>=4.0.0',
            'mypy>=0.900',
        ],
    },
    keywords='sprites container execution websocket api-client',
    project_urls={
        'Documentation': 'https://docs.sprites.dev',
        'Source': 'https://github.com/sprite-env/python-sdk',
        'Bug Reports': 'https://github.com/sprite-env/python-sdk/issues',
    },
)