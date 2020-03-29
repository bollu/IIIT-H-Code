#!/usr/bin/env python2.7
import pyspark
from pyspark.sql import *
import argparse


parser = argparse.ArgumentParser(description='solve question.')
parser.add_argument('outpath', type=str, metavar='O', help='path to output')
parser.add_argument('--ncpu',  type=int, default=2,
                    help='number of cpus')

args = parser.parse_args()

spark = SparkSession.builder \
  .master("local") \
  .appName("Word Count") \
  .config("spark.some.config.option", "some-value") \
  .getOrCreate()


airports = spark.read.csv("Dataset/airports.csv",
        header=True,
        inferSchema=True)

df = airports.groupby("COUNTRY").count()
df.toPandas().to_csv(args.outpath)

