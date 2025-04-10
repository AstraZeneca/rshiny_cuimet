# CUI-MET R shiny app
# CUI Dose Optimization Approach for Multiple-dose Randomized Trial Designs.
# Programmer: Fanni Zhang
# date: 06/13/2023, initial version v0, basic plot with marginal probs
# Update: 
# 10/02/2023 - add features: bootstrap CI option, utility summary, table download 
# 10/23/2023 - add % optimal dose selected in the utility bootstrap table
# 11/16/2023 - as Mike suggested, optimize the boot function without reshaping data,
#              reset seed everytime boot is run to allow reproducibility
#              remove sys.sleep()
# 03/22/2024 - add modeling approaches 
#              add functions gen.logit and gen.DRmod  
#              logistic (linear/quadratic) based on Mike's constrained logit code 
#              Emax, exponential using DR models from DoseFinding package
#              make changes to the functions gen.utility, gen.plot accordingly
#              include selected method in the download table summary
# 04/02/2024 - update points in the plots
# 05/31/2024 - use the "general" approach for a binary regression in gen.DRmod 
#              as illustrated at https://www.rdocumentation.org/packages/DoseFinding/versions/1.1-1/topics/fitMod
# 06/13/2024 - update ll.logit.constrained and gen.logit functions to incorporate flexible monotonic assumption
#              add input options to allow user to define the monotonic assumptions when a logit model is selected
# 09/03/2024 - incorporate method selection for each ED
# 10/28/2024 - add plot download
# 11/01/2024 - update code to handle endpoint data with missing records

library(shiny)
library(dplyr)
library(shinyhelper)
library(ggplot2)
library(tidyverse)
library(boot)
library(DoseFinding)
set.seed(12345)

# global definition for decimal format
# can be defined as an input parameter if needed
ndecimal <- 2
fmt <- paste0("%.", ndecimal, "f")

# global model label setting
model.label <- c("Empirical Method", 
                 "Logit Linear Model", 
                 "Logit Quadratic Model", 
                 "Emax Model", 
                 "Exponential Model")
model.char <- c("empirical", "logit.linear", "logit.quad", "emax", "exponential") 

#' ll.logit.constrained 
#' This function calculates the log-likelihood for a logistic model with optional constraints 
#' on parameter transformations to enforce monotonicity. It supports both linear and quadratic 
#' logit models.
#'
#' @param par A numeric vector of beta parameters in the logistic model.
#' @param y A numeric vector of binary endpoint values (0 or 1).
#' @param x A matrix representing the model design, including intercepts and predictor variables.
#' @param model A character string specifying the model type. Options are `"logit.linear"` (default) 
#' or `"logit.quad"`.
#' @param monotonic A logical value indicating whether to enforce a monotonicity constraint 
#' (default is `TRUE`).
#'
#' @return The computed log-likelihood value for the specified logistic model, potentially penalized 
#' if monotonicity constraints are violated in the quadratic model.
#' @details
#' - For `"logit.linear"`, if `monotonic = TRUE`, the second parameter is transformed 
#'   using `exp(par[2])` to enforce a positive coefficient.
#' - For `"logit.quad"`, if `monotonic = TRUE`, the derivative constraints ensure that 
#'   the probability function remains monotonic across the range of `Dose`. A heavy penalty is 
#'   applied to the log-likelihood if the constraints are violated.
ll.logit.constrained <- function(par, y, x, model = "logit.linear", monotonic = TRUE){
  # decide on the par transformation based on monotonicity constraint
  if(model == "logit.linear"){
    if(monotonic){
      betas <- c(par[1], exp(par[2])) # only intercept is unconstrained, b0=par1 and b1=exp(par2), b1>0
    }else{
      betas <- par # no constraints
    } 
    
    # calculate the predicted probabilities
    p <- plogis(x %*% betas)
    
    # compute the log-likelihood
    ll <- sum(y * log(p) + (1 - y) * log(1 - p))
  }else if(model == "logit.quad"){
    betas <- par
    # apply parameter transformation based on the monotonicity requirement
    if(monotonic){
      # logit(p) = b0 + b1*X + b2*X^2 
      # the derivative logit function wrt X is b1+2*b2*X, which needs to be positive across all values of X
      # ensure both b1+2*b2*dose.min and b1+2*b2*dose.max positive
      dose.min <- min(x[, "Dose"])
      dose.max <- max(x[, "Dose"])
      min.derivative <- betas[2] + 2 * betas[3] * dose.min
      max.derivative <- betas[2] + 2 * betas[3] * dose.max
      
      # ensure derivative does not go non-positive over the range of X
      if(min.derivative <= 0 | max.derivative <= 0){
        penalty <- 1e6 * (min(min.derivative, max.derivative)^2)  # penalize non-positive derivatives heavily
      }else{
        penalty <- 0
      }
    }else{
      penalty <- 0
    }
    
    # calculate the predicted probabilities
    p <- plogis(x %*% betas)
    
    # compute the log-likelihood with the penalty for non-monotonicity
    ll <- sum(y * log(p) + (1 - y) * log(1 - p)) - penalty
  }
  ll
}

#' gen.logit
#' This function estimates the predicted probabilities from a logistic model, 
#' optionally enforcing monotonic constraints on parameter estimates. It supports 
#' both linear and quadratic logistic regression models.
#'
#' @param EP A character string specifying the endpoint variable name in the dataset.
#' @param model A character string indicating the type of logistic model to fit. 
#'   Options are `"logit.linear"` (default) or `"logit.quad"`.
#' @param data A data frame containing the predictor variable `Dose` and the 
#'   specified endpoint `EP`. If `model = "logit.quad"`, an additional `DoseSq` 
#'   column is created.
#' @param monotonic A logical value specifying whether to enforce a monotonicity 
#'   constraint (default is `TRUE`).
#'
#' @return A numeric vector containing the estimated marginal probabilities 
#'   for the specified endpoint across unique dose levels.
#' @details
#' - The function first prepares the design matrix for logistic regression.
#' - If `model = "logit.quad"`, a quadratic term `DoseSq` is added.
#' - Missing values in `EP` are removed from the dataset.
#' - The function fits a constrained logistic regression model using `optim()`, 
#'   maximizing the log-likelihood computed via `ll.logit.constrained()`.
#' - The estimated model coefficients are used to compute predicted probabilities 
#'   at unique dose levels.
gen.logit <- function(EP, model = "logit.linear", data, monotonic = TRUE){
  # set up covariates and par initial values
  if(model == "logit.linear"){
    xvar <- "Dose"
    par.start <- c(-2, 0)
  }else if(model == "logit.quad"){
    data[, "DoseSq"] <- data[, "Dose"]^2
    xvar <- c("Dose", "DoseSq")
    par.start <- c(-2, 0, 0)
  }
  
  # extract data with non-missing records for the specified EP
  if(sum(is.na(data[,EP]))>0) data <- data[!is.na(data[,EP]), ]
  
  # define model formula and design matrix
  str.x <- paste(xvar, collapse = "+", sep = "")
  formula.logit <- as.formula(paste(EP, "~", str.x, sep=""))
  x <- model.matrix(formula.logit, data = data)
  
  # fit constrained logit model
  logit.constrained.optim <- optim(par = par.start, ll.logit.constrained,
                                   y = data[, EP], x = x, model = model, 
                                   monotonic = monotonic, control = list(fnscale = -1))
  if(model == "logit.linear" & monotonic){
    betas <- c(logit.constrained.optim$par[1], exp(logit.constrained.optim$par[2]))
  }else{
    betas <- logit.constrained.optim$par
  }
  
  # calculate the predicted probabilities
  doses <- unique(data$Dose)
  xdose <- cbind(1, doses)
  if(model == "logit.quad") xdose <- cbind(xdose, doses^2)
  pEP <- c(plogis(xdose %*% betas))
  pEP
  #fit.logit <- glm(formula.logit, data = data, family = "binomial")
  #betas.glm <- coefficients(fit.logit)
  #list(betas = betas, betas.glm = betas.glm, pEP = pEP)
}

#' gen.DRmod
#' This function estimates the predicted probabilities from a dose-response (DR) model, 
#' using the `DoseFinding` package. It supports Emax and Exponential models.
#'
#' @param EP A character string specifying the endpoint variable name in the dataset.
#' @param model A character string indicating the dose-response model to fit. 
#'   Options are `"emax"` (default) or `"exponential"`.
#' @param data A data frame containing dose levels (`Dose`) and the corresponding endpoint (`EP`).
#'
#' @return A numeric vector of predicted marginal probabilities for the endpoint at each dose level.
#' @details
#' - The function first fits a generalized linear model (GLM) without an intercept to estimate 
#'   log-odds at each dose level.
#' - It extracts dose-specific estimates (`mu.hat`) and their covariance matrix (`vcov.hat`).
#' - Using these estimates, it fits the specified dose-response model (`emax` or `exponential`).
#' - Predicted probabilities are computed on the logit scale and then transformed to probability scale.
gen.DRmod <- function(EP, model = "emax", data){
  # use the "general" approach for a binary regression
  # fit glm without intercept first to reflect the log-odds of outcome at each specific dose level
  formula.glm <- as.formula(paste0(EP, " ~ factor(Dose) - 1"))
  fit.glm <- glm(formula.glm, data = data, family = binomial)
  mu.hat <- coef(fit.glm)
  vcov.hat <- vcov(fit.glm)
  
  # ensure a consistent order of dose levels in both model fittings
  doses <- as.numeric(levels(factor(data$Dose)))
  
  # fit Emax or exponential model using the logit scale estimates and corresponding estimated covariance matrix
  fit <- fitMod(dose = doses, 
                resp = mu.hat, S = vcov.hat, model = model, 
                type = "general", bnds = defBnds(max(doses))[[model]])
  
  # calculate predicted probabilities on logit scale
  pEP.logit <- predict(fit, doseSeq = doses, predType = "ls-means") 
  
  # transform value to predicted probability
  pEP <- 1 / (1 + exp(-pEP.logit))
  pEP
}

#' gen.utility
#' This function calculates predicted marginal probabilities for multiple endpoints 
#' across dose levels using specified models, computes utility scores, and outputs 
#' the results in both wide and long formats for analysis and visualization.
#'
#' @param data A data frame containing dose levels (`Dose`) and multiple endpoints.
#' @param wEPs A numeric vector specifying weights applied to each endpoint 
#'   for the weighted utility calculation.
#' @param models A named vector specifying the model to be used for each endpoint. 
#'   Options include `"logit.linear"`, `"logit.quad"`, `"emax"`, `"exponential"`, and `"empirical"`.
#' @param EPs.mono A character vector specifying which endpoints should enforce 
#'   the monotonicity assumption.
#'
#' @return A list containing:
#' - `data.sum`: A data frame (wide format) with marginal probabilities for each endpoint and utility scores.
#' - `data.sum.long`: A data frame (long format) for visualization purposes.
#' - `EPs`: A character vector of endpoint names from the input data.
#' - `Metrics`: A character vector of endpoint names, flipped toxicity, and utility score types used in other app functions.
#'
#' @details
#' - Computes observed marginal probabilities for each dose level.
#' - Predicts marginal probabilities for each endpoint using the specified model.
#' - If `model = "empirical"`, observed means are used.
#' - If `model = "logit.linear"` or `"logit.quad"`, logistic regression is used (`gen.logit()`).
#' - If `model = "emax"` or `"exponential"`, dose-response modeling is used (`gen.DRmod()`).
#' - Toxicity values are flipped (1 - Toxicity) for consistent interpretation across endpoints.
#' - Computes both unweighted (`UtilityMean`) and weighted (`UtilityWeightedMean`) utility scores.
#' - Organizes output in wide and long formats to facilitate further analysis and visualization.
gen.utility <- function(data, wEPs, models, EPs.mono){
  # get endpoint names from input data
  EPs <- setdiff(colnames(data), c("ID", "Dose"))
  
  # get observed marginal prob per dose level in data.sum.obs
  data.sum <- data %>% group_by(Dose) %>% summarise(across(all_of(EPs), mean, na.rm = TRUE))
  data.sum.obs <- data.sum
  
  # calculate predicted marginal probabilities based on specified models
  pEP.mat <- sapply(EPs, function(ep) {
    current.model <- models[EPs %in% ep]
    if(current.model == "empirical"){
      pull(data.sum, ep)
    } else if(current.model %in% c("logit.linear", "logit.quad")) {
      gen.logit(EP = ep, model = current.model, data = data, monotonic = ep %in% EPs.mono)
    } else if(current.model %in% c("emax", "exponential")) {
      gen.DRmod(EP = ep, model = current.model, data = data)
    }
  })
  
  data.sum[, EPs] <- data.frame(pEP.mat)
  
  # flip toxicity value to follow same direction with other EPs - 1 indicating improvement
  data.sum$'1-Toxicity' <- 1 - data.sum$Toxicity
  data.sum.obs$'1-Toxicity' <- 1 - data.sum.obs$Toxicity
  
  # generate utility mean and utility weighted mean
  EPs.util <- gsub("Toxicity", "1-Toxicity", EPs)
  data.sum$UtilityMean <- apply(data.sum[,EPs.util], 1, mean)
  data.sum$UtilityWeightedMean <- c(as.matrix(data.sum[,EPs.util]) %*% wEPs)
  
  # include utility mean and weighted mean in data.sum.obs for plotdata set 
  data.sum.obs$UtilityMean <- data.sum$UtilityMean 
  data.sum.obs$UtilityWeightedMean <- data.sum$UtilityWeightedMean
  
  # put "1-Toxicity" next to "Toxicity"
  metrics <- c(EPs, "1-Toxicity", "UtilityMean", "UtilityWeightedMean")
  tox.index <- which(metrics == "Toxicity")
  metrics.sort <- c(metrics[1:tox.index], "1-Toxicity",
                    metrics[!metrics %in% c(metrics[1:tox.index], "1-Toxicity")])
  data.sum <- data.sum[, c("Dose", metrics.sort)]
  
  data.sum.long <- data.frame(
    Dose = rep(data.sum$Dose, each = length(metrics.sort)),
    Metric = rep(metrics.sort, nrow(data.sum)),
    MarginalProbability = c(t(data.sum[, metrics.sort]))
  )
  
  # include observed margina prob
  data.sum.long$obsMP <- c(t(data.sum.obs[, metrics.sort]))
  
  data.sum <- data.frame(data.sum,check.names = F)
  data.sum.long <- data.frame(data.sum.long,check.names = F)
  out <- list(data.sum = data.sum, data.sum.long = data.sum.long, 
              EPs = EPs, Metrics = metrics.sort)
  out
}

#' gen.utility.boot
#' This function performs bootstrapping to estimate the utility mean and weighted mean 
#' for multiple endpoints across dose levels. It follows the requirements of the `boot` package 
#' and outputs results in long format.
#'
#' @param data A data frame containing dose levels (`Dose`) and multiple endpoints.
#' @param wEPs A numeric vector specifying weights applied to each endpoint for the weighted utility calculation.
#' @param indices A numeric vector of resampled indices, as required by the `boot()` function.
#' @param models A named vector specifying the model to be used for each endpoint. 
#'   Options include `"logit.linear"`, `"logit.quad"`, `"emax"`, `"exponential"`, and `"empirical"`.
#' @param EPs.mono A character vector specifying which endpoints should enforce 
#'   the monotonicity assumption.
#'
#' @return A numeric vector of bootstrapped estimates for marginal probabilities, 
#' utility mean, and weighted mean, formatted in long format.
#'
#' @details
#' - The function applies bootstrapping by resampling data using the provided `indices`.
#' - Computes observed marginal probabilities per dose level.
#' - Predicts marginal probabilities for each endpoint using the specified model.
#' - If `model = "empirical"`, observed means are used.
#' - If `model = "logit.linear"` or `"logit.quad"`, logistic regression is used (`gen.logit()`).
#' - If `model = "emax"` or `"exponential"`, dose-response modeling is used (`gen.DRmod()`).
#' - Toxicity values are flipped (`1 - Toxicity`) for consistent interpretation across endpoints.
#' - Computes both unweighted (`UtilityMean`) and weighted (`UtilityWeightedMean`) utility scores.
#' - Ensures `UtilityWeightedMean` is identical to `UtilityMean` when all endpoint weights are equal.
#' - Organizes output in long format to facilitate further analysis and visualization.
gen.utility.boot <- function(data, wEPs, indices, models, EPs.mono){
  data.boot <- data[indices, ]
  
  # get endpoint names from input data
  EPs <- setdiff(colnames(data.boot), c("ID", "Dose"))
  
  # get observed marginal prob per dose level in data.sum.obs
  data.boot.sum <- data.boot %>% group_by(Dose) %>% summarise(across(all_of(EPs), mean, na.rm = TRUE))
  data.boot.sum.obs <- data.boot.sum
  
  # calculate predicted marginal probabilities based on specified models
  pEP.mat <- sapply(EPs, function(ep) {
    current.model <- models[EPs %in% ep]
    if(current.model == "empirical"){
      pull(data.boot.sum, ep)
    } else if(current.model %in% c("logit.linear", "logit.quad")) {
      gen.logit(EP = ep, model = current.model, data = data.boot, monotonic = ep %in% EPs.mono)
    } else if(current.model %in% c("emax", "exponential")) {
      gen.DRmod(EP = ep, model = current.model, data = data.boot)
    }
  })
  
  data.boot.sum[, EPs] <- data.frame(pEP.mat)
  
  # flip toxicity value to follow same direction with other EPs - 1 indicating improvement
  data.boot.sum$'1-Toxicity' <- 1 - data.boot.sum$Toxicity
  data.boot.sum.obs$'1-Toxicity' <- 1 - data.boot.sum.obs$Toxicity
  
  EPs.util <- gsub("Toxicity", "1-Toxicity", EPs)
  data.boot.EP <- data.boot.sum[, EPs.util]
  
  # generate utility mean and utility weighted mean
  data.boot.sum.obs$UtilityMean <- data.boot.sum$UtilityMean <- apply(data.boot.EP, 1, mean)
  
  # ensure UWM is identical to UM to avoid accuracy issue in dose selection when EPs have all equal weights
  if(sd(wEPs) == 0){
    data.boot.sum$UtilityWeightedMean <- data.boot.sum$UtilityMean
    data.boot.sum.obs$UtilityWeightedMean <- data.boot.sum$UtilityMean
  }else{
    data.boot.sum$UtilityWeightedMean <- c(as.matrix(data.boot.EP) %*% wEPs)
    data.boot.sum.obs$UtilityWeightedMean <- c(as.matrix(data.boot.EP) %*% wEPs)
  }

  # put "1-Toxicity" next to "Toxicity"
  metrics <- c(EPs, "1-Toxicity", "UtilityMean", "UtilityWeightedMean")
  tox.index <- which(metrics == "Toxicity")
  metrics.sort <- c(metrics[1:tox.index], "1-Toxicity",
                    metrics[!metrics %in% c(metrics[1:tox.index], "1-Toxicity")])
  data.boot.sum <- data.boot.sum[, c("Dose", metrics.sort)]

  out <- c(t(data.boot.sum[, metrics.sort]))
  
  return(out)
}

#' gen.plot
#' This function creates a utility graph based on the predicted and observed marginal 
#' probabilities of multiple endpoints across dose levels. The utility scores are visualized 
#' alongside endpoint probabilities.
#'
#' @param plotdata A data frame in long format containing dose levels, endpoints, 
#'   predicted marginal probabilities, and observed marginal probabilities. 
#'   This should be the output from `gen.utility()`.
#' @param EPs A character vector specifying the endpoint names included in the plot.
#' @param wEPs A numeric vector specifying weights applied to each endpoint.
#' @param mEPs A character vector specifying the method used for each endpoint.
#' @param title A character string specifying the title of the plot (default: `"CUI-MET Graph"`).
#'
#' @return A `ggplot` object displaying the utility graph.
gen.plot <- function(plotdata, EPs, wEPs, mEPs, title = "CUI-MET Graph"){
  # extract EP labels with "1-Toxicity" excluded
  EPs.label <- unique(plotdata$Metric)
  EPs.label <- EPs.label[-which(EPs.label == "1-Toxicity")]
  
  plotdata <- plotdata %>% filter(Metric != "1-Toxicity") %>% 
    mutate(MarginalProbability = as.numeric(MarginalProbability),
           Metric = factor(Metric, levels = EPs.label))
  # define axis limits
  ymin <- 0
  ymax <- 1
  xmin <- min(plotdata$Dose)
  xmax <- length(unique(plotdata$Dose))
  
  # define method/weight labels
  wEPs <- as.numeric(wEPs)
  str <- paste0(EPs,": ", mEPs, " (w=", round(wEPs, 2), ") \n")
  str[length(str)] <- paste0(EPs[length(EPs)], ": ", mEPs[length(mEPs)], " (w=", round(wEPs[length(EPs)], 2), ")")
  run.str <- paste0('weight.label<- "Method (Weight): \n ', toString(str), '"')
  run.str <- gsub("\\,", "", run.str)
  eval(parse(text = run.str))
  
  # set a color palette, line types and line sizes
  hues <- seq(15, 375, length = length(EPs) + 1)
  gg_color_hue <- hcl(h = hues, l = 65, c = 100)[1:length(EPs)]
  linetype <- c(rep("solid", length(EPs)), "dashed", "solid")
  linesize <- c(rep(0.3, length(EPs)), rep(0.6, 2))
  
  plot <- ggplot() +
    geom_point(data = plotdata, aes(x = Dose, y = obsMP, group = Metric, colour = Metric), size = 1.5) +
    geom_line(data = plotdata, aes(x = Dose, y = MarginalProbability, group = Metric, colour = Metric, linetype = Metric, linewidth = Metric)) +
    xlab("Dose Level") + ylab("Marginal Probability/CUI") +
    theme_bw() + ggtitle(title) +
    coord_cartesian(ylim = c(ymin, ymax)) +
    scale_y_continuous(breaks = seq(0, 1, by = 0.1)) +
    scale_x_continuous(breaks = seq(0, xmax, by = 1)) +
    scale_color_manual("", values = c(gg_color_hue, "gray50", "black")) +
    scale_linetype_manual("", values = linetype, guide = "none") +
    scale_linewidth_manual("", values = linesize, guide = "none") +
    annotate("text", x = xmin, y = 0.9, label = weight.label, size = 4, hjust = 0) + 
    theme(axis.title.x = element_text(size = 16), axis.text.x = element_text(size = 14),
          axis.title.y = element_text(size = 16), axis.text.y = element_text(size = 14),
          plot.title = element_text(size = 20, hjust = 0.5),
          plot.caption = element_text(size = 12, hjust = 0.5),
          legend.text = element_text(size = 14),
          legend.position = "bottom") +
    guides(colour = guide_legend(override.aes = list(linetype = linetype))) +
    labs(caption = "Please note that we use the flipped toxicity (1-toxicity) when calculating utility mean and weighted mean.")
  
  return(plot)
}

#' gen.plot.ci
#' This function creates a utility graph incorporating bootstrap confidence intervals (CIs) 
#' for predicted and observed marginal probabilities of multiple endpoints across dose levels.
#'
#' @param plotdata A data frame in long format containing dose levels, endpoints, 
#'   predicted marginal probabilities, and observed marginal probabilities. 
#'   This should be the output from `gen.utility()`.
#' @param CI A matrix containing lower and upper confidence intervals for each endpoint, 
#'   derived from bootstrapping.
#' @param EPs A character vector specifying the endpoint names included in the plot.
#' @param wEPs A numeric vector specifying weights applied to each endpoint.
#' @param mEPs A character vector specifying the method used for each endpoint.
#' @param title A character string specifying the title of the plot (default: `"CUI-MET Graph"`).
#'
#' @return A `ggplot` object displaying the utility graph with bootstrap confidence intervals.
gen.plot.ci <- function(plotdata, CI, EPs, wEPs, mEPs, title = "CUI-MET Graph"){
  # extract EP labels with "1-Toxicity" excluded
  EPs.label <- unique(plotdata$Metric)
  toxflip.index <- which(plotdata$Metric == "1-Toxicity")
  EPs.label <- EPs.label[-which(EPs.label == "1-Toxicity")]
  plotdata <- plotdata %>% filter(Metric != "1-Toxicity") %>% 
    mutate(MarginalProbability = as.numeric(MarginalProbability),
           Metric = factor(Metric, levels = EPs.label))
  # add CI into plotdata
  plotdata$LCI <- CI[1, -toxflip.index]
  plotdata$UCI <- CI[2, -toxflip.index]
  
  # define axis limits
  ymin <- 0
  ymax <- 1
  xmin <- min(plotdata$Dose)
  xmax <- length(unique(plotdata$Dose))

  # define method/weight labels
  wEPs <- as.numeric(wEPs)
  str <- paste0(EPs,": ", mEPs, " (w=", round(wEPs, 2), ") \n")
  str[length(str)] <- paste0(EPs[length(EPs)], ": ", mEPs[length(mEPs)], " (w=", round(wEPs[length(EPs)], 2), ")")
  run.str <- paste0('weight.label<- "Method (Weight): \n ', toString(str), '"')
  run.str <- gsub("\\,", "", run.str)
  eval(parse(text = run.str))
  
  # set colors, line types and sizes
  hues <- seq(15, 375, length = length(EPs) + 1)
  gg_color_hue <- hcl(h = hues, l = 65, c = 100)[1:length(EPs)]
  linetype <- c(rep("solid", length(EPs)), "dashed", "solid")
  linesize <- c(rep(0.3, length(EPs)), rep(0.6, 2))
  
  pd <- position_dodge(0.1)
  plot <- ggplot() +
    geom_point(data = plotdata,aes(x = Dose, y = MarginalProbability, group = Metric, colour = Metric), size = 0.1, position = pd) +
    geom_point(data = plotdata, aes(x = Dose, y = obsMP, group = Metric, colour = Metric), size = 1.5, position = pd) +
    geom_line(data = plotdata, aes(x = Dose, y = MarginalProbability, group = Metric, colour = Metric, linetype = Metric, linewidth = Metric), position = pd) +
    geom_errorbar(data = plotdata, aes(x = Dose, y = MarginalProbability, ymin = LCI, ymax = UCI, group = Metric, colour = Metric, linetype = Metric), width = .1, position = pd) +
    xlab("Dose Level") + ylab("Marginal Probability/CUI") +
    theme_bw() + ggtitle(title) +
    coord_cartesian(ylim = c(ymin, ymax)) +
    scale_y_continuous(breaks = seq(0, 1, by = 0.1)) +
    scale_x_continuous(breaks = seq(0, xmax, by = 1)) +
    scale_color_manual("", values = c(gg_color_hue, "gray50", "black")) +
    scale_linetype_manual("", values = linetype, guide = "none") +
    scale_linewidth_manual("", values = linesize, guide = "none") +
    annotate("text", x = xmin, y = 0.9, label = weight.label, size = 4, hjust = 0)+ 
    theme(axis.title.x = element_text(size = 16), axis.text.x = element_text(size = 14),
          axis.title.y = element_text(size = 16), axis.text.y = element_text(size = 14),
          plot.title = element_text(size = 20,hjust = 0.5),
          plot.caption = element_text(size = 12, hjust = 0.5),
          legend.text = element_text(size = 14),
          legend.position = "bottom") +
    guides(colour = guide_legend(override.aes = list(linetype = linetype, fill = NA))) +
    labs(caption = "Please note that we use the flipped toxicity (1-toxicity) when calculating utility mean and weighted mean.")
  
  return(plot)
}

#==================================================================

# define UI for application
ui <- fluidPage(
  
  # application title with logo
  titlePanel(
    title = div(
      img(height = 50, src = "az_header.jpg"), 
      h2("CUI Dose Optimization Approach for Multiple-Dose, Multiple-Outcome Randomized Trial Designs")
    ), 
    "CUIMET"
  ),
  
  # main navigation panel
  navbarPage("",
             
    # CUI-MET Tab
    tabPanel("CUI-MET (Beta Version)",
             
      sidebarLayout(
        
        # sidebar Panel
        sidebarPanel(
          
          # file input with helper text
          fileInput("file", "Input File", accept = c(".csv")) %>%
            helper(type = "inline", content = 
              "Input data should be a data frame saved in a .csv format. 
              For reference, please access an example dataset by clicking 
              on the 'Example Data' hyperlink. This will give you a clear 
              understanding of the desired data structure."
            ),
          
          # example data link
          div(style = "margin-top: -20px"),
          tags$a(
            href = 'data/CUIMET_example_binarydata.csv', 
            target = '_blank', 
            'Example Data', 
            download = 'CUIMET_example_binarydata.csv'
          ),
          
          br(), br(), br(),
          
          # UI Outputs for Endpoint Weights and Methods
          uiOutput("wEPtitle"),
          uiOutput("weightEP"),
          uiOutput("noteweightEP"),
          br(),
          uiOutput("mEPtitle"),
          uiOutput("methodEP"),
          br(),
          uiOutput("plottitle")
        ),
        
        # main Panel
        mainPanel(
          
          uiOutput("texttitle"),
          br(),
          plotOutput("utilityplot"),
          uiOutput("ci"),
          uiOutput("downloadCUIplot"),
          br(),
          
          # UI Outputs for Utility Table and Confidence Intervals
          uiOutput("utilitytitle"),
          conditionalPanel(
            condition = "input.CIind == '1'",
            uiOutput("CItitle")
          ),  
          uiOutput("downloadCUI"),
          br()
        )
      )
    ),
    
    # user guide tab
    tabPanel("User Guide", 
      uiOutput("help")
    )
  )
)

server <- function(input, output,session) {
  
  observe_helpers(withMathJax = TRUE)
  
  # input validation
  input.valid <- reactive({
    infile <- input$file
    if (is.null(infile)) {
      return(FALSE)  # return FALSE if no file is uploaded
    }
    
    # load in data
    data <- read.csv(infile$datapath, stringsAsFactors = FALSE, check.names = FALSE)
    data <- data.frame(data, stringsAsFactors = FALSE)
    
    # check for required columns
    required.cols <- c("ID", "Dose", "Toxicity", "Efficacy")
    if (!all(required.cols %in% colnames(data))) {
      shiny::showNotification("Warning: Please include at least 4 variables - ID, Dose, Toxicity, and Efficacy in the input data for the functionality of the shiny app.", 
                              duration = 7, type = "error")
      return(FALSE)  # return FALSE as the validation did not pass for required columns
    }
    
    # check if 'Dose' column has consecutive natural numbers starting from 1
    if (!identical(as.numeric(sort(unique(data$Dose))), seq(from = 1, to = max(data$Dose), by = 1))) {
      shiny::showNotification("Warning: Dose should be numerical values ranging from 1 to the highest dose level used in the study.", 
                              duration = 7, type = "error")
      return(FALSE)  # return FALSE as 'Dose' validation did not pass
    }
    
    # check if other columns except 'ID' and 'Dose' are binary (0/1)
    binary.cols <- setdiff(colnames(data), c("ID", "Dose"))
    if (any(sapply(data[, binary.cols, drop = FALSE], function(x) !all(x %in% c(0, 1, NA))))) {
      shiny::showNotification("Warning: All endpoints should be binary (0/1).", 
                              duration = 7, type = "error")
      return(FALSE)  # return FALSE as binary validation did not pass
    }
    
    # check if each dose level has at least min.sample.size non-missing observations for each endpoint
    min.nmobs <- 10 # minimum of non-missing observations
    missing.check <- data %>%
      group_by(Dose) %>%
      summarise(across(all_of(binary.cols), ~ sum(!is.na(.)), .names = "count_{.col}"))
    # check if any dose level has insufficient non-missing data
    if (any(missing.check %>% select(starts_with("count_")) < min.nmobs)) {
      insufficient.data <- missing.check %>%
        pivot_longer(-Dose, names_to = "Endpoint", values_to = "Count") %>%
        filter(Count < min.nmobs)
      
      # format the insufficient data message for the notification
      warning.msg <- paste0(
        "Warning: Insufficient sample size due to missing data for one or more endpoints.\n",
        "Each dose level requires at least ", min.nmobs, " non-missing observations.\n",
        "The following dose levels and endpoints have fewer than ", min.nmobs, " non-missing observations:\n\n",
        paste0("Dose Level ", insufficient.data$Dose, ", Endpoint: ", 
               gsub("count_", "", insufficient.data$Endpoint), 
               " - Only ", insufficient.data$Count, " non-missing observations.\n", collapse = "")
      )
      
      # display warning notification in Shiny
      shiny::showNotification(warning.msg, duration = 10, type = "error")
      return(FALSE)  # return FALSE as the validation did not pass
    }
    
    return(TRUE)  # return TRUE as all validations passed
  })
  
  # observe the validation flag and show a message if false
  observeEvent(input.valid(), {
    infile <- input$file
    if (is.null(infile)) return(NULL)
    if (!input.valid()) {
      # display a warning message to the user
      shiny::showNotification("Input validation failed: Please review the warning message for specific issues and adjust your data accordingly.", 
                              duration = 7, type = "error")
    }
  })
  
  # input data for upload feature, extract EPs 
  indata <- reactive({
    infile <- input$file
    data.list <- NULL
    if (is.null(infile) | !input.valid()) return(NULL)
    
    # load in data
    data <- read.csv(infile$datapath, stringsAsFactors = F, check.names = F)
    data <- data.frame(data, stringsAsFactors = F)
    
    # sort data by Dose level and ID to ensure a consistent order in all modeling approaches
    data <- data[order(data$Dose, data$ID), ]
    
    # extract endpoints
    EPs <- setdiff(colnames(data), c("ID", "Dose"))
    nEP <- length(EPs)
    
    # return a list including data, endpoints and number of endpoints
    data.list <- list(data = data, EPs = EPs, nEP = nEP)
    data.list
  })
  
  # add weighting title
  output$wEPtitle <- renderUI({
    data.list <- indata()
    if(!is.null(data.list)){
      h4(em("Weighting")) %>%
        helper(type = "inline", content = "Please adjust the weighting in increments of 0.1, 
               with higher values indicating greater importance for a particular endpoint. ")
    }
  })
  
  # input weighting parameter
  output$weightEP <- renderUI({
    data.list <- indata()
    if(!is.null(data.list)){
      data <- indata()$data
      EPs <- setdiff(colnames(data), c("ID", "Dose"))
      nEP <- length(EPs)
      wEP.vars <- paste0("wEP", 1:nEP)
      lapply(1:nEP, function(i) {
        sliderInput(wEP.vars[i], paste0("Weighting of ", EPs[i]), min = 0, max = 5, value = 1, step = 0.1)
      })
    }
  })
  
  # add note text for weightings
  output$noteweightEP <- renderUI({
    data.list <- indata()
    if(!is.null(data.list)){
      helpText("Entered weightings are normalized to add up to one.")
    }
  })
  
  # add method title
  output$mEPtitle <- renderUI({
    data.list <- indata()
    if(!is.null(data.list)){
      h4(em("Method")) %>%
        helper(type = "inline", content = "Please select methods for each endpoint and indicate whether a monotonicity assumption 
               is required for those endpoints where a logit model is selected. Note that Toxicity is always assumed to be monotonic.")
    }
  })
  
  # input method for each ED
  output$methodEP <- renderUI({
    data.list <- indata()
    if(!is.null(data.list)){
      data <- indata()$data
      EPs <- setdiff(colnames(data), c("ID", "Dose"))
      nEP <- length(EPs)
      mEP.vars <- paste0("mEP", 1:nEP)
      mono.vars <- paste0("monoEP", 1:nEP)
      lapply(1:nEP, function(i) {
        fluidRow(
          column(6,
                 selectInput(mEP.vars[i], EPs[i], choices = model.label, selected = model.label[1])
          ),
          column(6,
                 conditionalPanel(
                   condition = sprintf("((input.%s == 'Logit Linear Model' || input.%s == 'Logit Quadratic Model') && ('%s' !== 'Toxicity'))", 
                                       mEP.vars[i], mEP.vars[i], EPs[i]),
                   checkboxInput(mono.vars[i], "Assume Monotonicity?")
                 )
          )
        )
      })
    }
  })
  
  # add user-defined title
  output$plottitle <- renderUI({
    data.list <- indata()
    if(!is.null(data.list)){
      textInput("plottitle", "Plot Title", "CUI-MET Graph")
    }
  })

  # reactive function for utility
  utility <- reactive({
    out.list <- NULL
    if(!is.null(indata()) & !is.null(input$wEP1)){
      EPs <- indata()$EPs
      nEP <- length(EPs)
      run.str <- paste0("sum.wEP <- ", gsub("\\,", "\\+", toString(paste0("input$wEP", 1:(nEP)))), "")
      eval(parse(text = run.str))
      data <- indata()$data
      EPs <- indata()$EPs
      nEP <- length(EPs) # repeated lines that needs updates
      run.str <- paste0("wEP.vec <- c(", toString(paste0("input$wEP", 1:nEP)), ")")
      eval(parse(text = run.str))
      if(sum.wEP == 0){
        wEP.vec <- rep(0, nEP)
      }else{
        wEP.vec <- wEP.vec/sum.wEP
      }
      
      run.str <- paste0("mEP.vec <- c(", toString(paste0("input$mEP", 1:nEP)), ")")
      eval(parse(text = run.str))
      
      run.str <- paste0("monoEP.vec <- c(", toString(paste0("input$monoEP", 1:nEP)), ")")
      eval(parse(text = run.str))
      
      EPs.model <- model.char[match(mEP.vec, model.label)]
      EPs.mono <- EPs[monoEP.vec]
      #print(EPs.model)
      #print(EPs.mono)
      
      out <- gen.utility(data = data, wEPs = wEP.vec, models = EPs.model, EPs.mono = EPs.mono)

      out.list <- list(out = out, wEPs = wEP.vec, mEPs = mEP.vec, EPs.mono = EPs.mono)
    }
    return(out.list)
    
  })
  
  # create output utility summary table
  output$utility <- renderTable({
    data.sum <- NULL
    if(!is.null(utility())){
      data.sum <- utility()$out$data.sum
      umax.index <- which.max(data.sum$UtilityMean)
      uwmax.index <- which.max(data.sum$UtilityWeightedMean)
      data.sum$UtilityMean <- sprintf(data.sum$UtilityMean, fmt = fmt)
      data.sum$UtilityWeightedMean <- sprintf(data.sum$UtilityWeightedMean, fmt = fmt)
      umax <- data.sum$UtilityMean[umax.index]
      uwmax <- data.sum$UtilityWeightedMean[uwmax.index]
      # change font color for the max utility and weighted utility
      data.sum$UtilityMean[umax.index] <- paste0("<font color=\"#FF0000\"><strong>", umax, "</strong></font>")
      data.sum$UtilityWeightedMean[uwmax.index] <- paste0("<font color=\"#FF0000\"><strong>", uwmax, "</strong></font>")
    }
    return(data.sum)
  }, rownames = F, colnames=T, sanitize.text.function = function(x){x})
  
  # reactive title for utility summary table
  output$utilitytitle <- renderUI({
    if(!is.null(utility())){
      wellPanel(
        p(strong("Utility Summary")),
        tableOutput("utility")
      )
    }  
  })
  
  # reactive function for utility with CI
  utilityboot <- reactive({
    out.boot <- NULL
    if(!is.null(indata()) & !is.null(input$wEP1) & !is.null(input$CIind)){
      data <- indata()$data
      EPs <- indata()$EPs
      nEP <- length(EPs)
      run.str <- paste0("sum.wEP <- ", gsub("\\,","\\+", toString(paste0("input$wEP", 1:(nEP)))), "")
      eval(parse(text = run.str))
      run.str <- paste0("wEP.vec <- c(", toString(paste0("input$wEP", 1:nEP)), ")")
      eval(parse(text = run.str))
      if(sum.wEP == 0){
        wEP.vec <- rep(0, nEP)
      }else{
        wEP.vec <- wEP.vec/sum.wEP
      }
      run.str <- paste0("mEP.vec <- c(", toString(paste0("input$mEP", 1:nEP)), ")")
      eval(parse(text = run.str))
      
      run.str <- paste0("monoEP.vec <- c(", toString(paste0("input$monoEP", 1:nEP)), ")")
      eval(parse(text = run.str))
      
      EPs.model <- model.char[match(mEP.vec, model.label)]
      EPs.mono <- EPs[monoEP.vec]
      #print(EPs.model)
      #print(EPs.mono)

      if(input$CIind == TRUE){
        results <- NULL
        wEPs <- wEP.vec
        # reset seed everytime boot is run to allow reproducibility
        set.seed(12345)

        # add progress bar
        withProgress(message = 'Bootstrapping in progress',
                     detail = 'This may take a while...', value = 0, {
                       nparts<-10
                       for (i in 1:nparts) {
                         results <- rbind(results,boot(data = data, statistic = gen.utility.boot, 
                                                       strata = data[, which(colnames(data) == "Dose")],
                                                       R = 1000/nparts, wEPs = wEPs, models = EPs.model, EPs.mono = EPs.mono)$t)
                         report.str <- paste(i*1000/nparts, " out of 1000 bootstrap replicates done")
                         incProgress(1/nparts, detail = report.str)
                       }
                     })
        pboot <- data.frame(results)
        data.sum.long <- utility()$out$data.sum.long
        
        # calculate probabilities for OBD selection
        pboot.u <- pboot[,which(data.sum.long$Metric == "UtilityMean")]
        pboot.uw <- pboot[,which(data.sum.long$Metric == "UtilityWeightedMean")]
        od.u <- as.matrix(apply(pboot.u, 1, which.max))
        od.uw <- as.matrix(apply(pboot.uw, 1, which.max))

        ndose <- length(unique(data.sum.long$Dose))
        odprop.u <- odprop.uw <- rep(0, ndose)
        index.u <- as.numeric(attributes(prop.table(table(od.u)))$dimnames$od.u)
        index.uw <- as.numeric(attributes(prop.table(table(od.uw)))$dimnames$od.uw)
        odprop.u[index.u] <- prop.table(table(od.u))
        odprop.uw[index.uw] <- prop.table(table(od.uw))
        
        pboot.mean <- colMeans(pboot)
        pboot.CI <- sapply(pboot, quantile, probs = c(0.025, 0.975))
        meanCI <- data.frame(cbind(pboot.mean, pboot.CI[1, ], pboot.CI[2, ]))
        meanCI.fmt <- apply(meanCI, 2, sprintf, fmt = fmt)
        pboot.meanCI <- paste0(meanCI.fmt[, 1], " (", meanCI.fmt[, 2],"-", meanCI.fmt[, 3], ")")
        pboot.sum <- cbind(data.sum.long[, c("Dose", "Metric")], pboot.meanCI)
        pboot.sum <- data.frame(pboot.sum)
        pboot.sum <- pboot.sum %>% pivot_wider(names_from = Metric, values_from = pboot.meanCI)
        umuwm <- c(UM = "UtilityMean", UWM = "UtilityWeightedMean")
        pboot.sum <- rename(pboot.sum, all_of(umuwm)) 
        pboot.sum <- bind_cols(pboot.sum,
                              '%OBD(UM)' = paste0(100*odprop.u, "%"),
                              '%OBD(UWM)' = paste0(100*odprop.uw, "%"))
        out.boot <- list(pboot = pboot, pboot.sum = pboot.sum)
        
      }else{
        out.boot <- NULL
      }
    }
    return(out.boot)
  })
  
  # create utility summary table from bootstrapping
  output$bootCI <- renderTable({
    pboot.sum <- NULL
    if(!is.null(utilityboot())){
      pboot.sum <- utilityboot()$pboot.sum
    }
    return(pboot.sum)
  }, rownames = F, colnames = TRUE,caption = "OBD: Optimal biologic dose. UM: Utility mean. UWM: Utility weighted mean. ")
  
  # reactive title for utility summary table from bootstrapping  
  output$CItitle <- renderUI({
    if(!is.null(utilityboot()) & !is.null(utility())){
      wellPanel(
        p(strong("Utility Summary from Bootstrapping")),
        div(tableOutput("bootCI"), style = "font-size:90%")
      )
    }  
  })
  
  # reactive panel for input summary
  output$texttitle <- renderUI({
    if(!is.null(indata())){
      wellPanel(
        p(strong("Input Summary")),
        uiOutput("text")
      )
    }  
  })
  
  # reactive input summary text
  output$text <- renderText({
    str <- NULL
    if(!is.null(indata()) & input.valid()){
      data <- indata()$data
      npts <- length(unique(data$ID))
      ndose <- length(unique(data$Dose))
      EPs <- indata()$EPs
      EPs.str <- toString(EPs)
      EPs.str <- gsub(paste0(", ", EPs[length(EPs)]), paste0(" and ", EPs[length(EPs)]), EPs.str)
      wEPs <- utility()$wEPs
      wEPs <- round(wEPs, 2)
      wEPs.str <- toString(wEPs)
      # replace the last comma with " and"
      wEPs.str <- sub(",([^,]*)$", " and\\1", wEPs.str)
      
      mEPs <- utility()$mEPs
      run.str <- paste0("mEPs <- c(", toString(paste0("input$mEP", 1:length(EPs))), ")")
      eval(parse(text = run.str))
      
      run.str <- paste0("monoEP.vec <- c(", toString(paste0("input$monoEP", 1:length(EPs))), ")")
      eval(parse(text = run.str))

      # Create a string for each endpoint with its model
      mEPs.str <- paste(mEPs, "for", EPs)
      # Format the list into a natural language list
      EPs.model.str <- paste(mEPs.str[1:length(EPs)-1], collapse=", ")
      EPs.model.str <- paste(EPs.model.str, "and", mEPs.str[length(EPs)])

      str1 <- paste0("In the study, ", npts, " subjects are assigned to ", ndose, " dose levels. ")
      str2 <- paste0("There are ", length(EPs), " endpoints: ", EPs.str, ". ")
      str3 <- paste0("The weights given to these endpoints are ", wEPs.str, ", respectively. ")
      str4 <- paste0("The utilities are calculated using the ", EPs.model.str, ".")
      
      EPs.mono <- EPs[monoEP.vec]
      if(length(EPs.mono)>0){
        if(length(EPs.mono) == 1){
          EPs.mono.str <- EPs.mono
        }else{
          EPs.mono.str <- toString(EPs.mono)
          EPs.mono.str <- gsub(paste0(", ", EPs.mono[length(EPs.mono)]), paste0(" and ", EPs.mono[length(EPs.mono)]), EPs.mono.str)
        }
        str4 <- paste0("The utilities are calculated using the ", EPs.model.str, " with a monotonic assumption for ", EPs.mono.str, ". <br/>")
      }
    }
    
    str <- paste0(str1, str2, str3, str4)
    HTML(str)
  })
  
  # utility graph wo/w CI
  output$utilityplot <- renderPlot({
    plot <- NULL
    if(!is.null(utility())){
      plotdata <- utility()$out$data.sum.long
      EPs <- utility()$out$EPs
      wEPs <- utility()$wEPs
      mEPs <- utility()$mEPs
      title <- input$plottitle
      plot <- gen.plot(plotdata = plotdata, EPs = EPs, wEPs = wEPs, mEPs = mEPs, title = title)
      if(!is.null(utilityboot())){
        pboot <- utilityboot()$pboot
        CI <- sapply(pboot, quantile, probs = c(0.025,0.975))
        plot <- gen.plot.ci(plotdata = plotdata, CI = CI, EPs = EPs, wEPs = wEPs, mEPs = mEPs, title = title)
      }
    }
    return(plot)
  })

  # user checkbox for displaying CI
  output$ci <- renderUI({
    if(!is.null(utility())){
      if(is.null(utilityboot())){
        checkboxInput("CIind", "Show 95% confidence intervals on the graph", FALSE)
      }else if(!is.null(utilityboot())){
        checkboxInput("CIind", "Show 95% confidence intervals on the graph", TRUE)
      }
    }  
  })
  
  # add download feature
  
  output$downloadCUIplot <- renderUI({
    if(!is.null(utility())){
      downloadButton('downloadplot', 'Save Plot')
    }  
  })
  
  output$downloadplot <- downloadHandler(
    filename = function() {
      paste('CUIMET_graph', '.png', sep='')
    },
    # Define the server-side processing function to save the plot
    content = function(file) {
      # Check if the plot data exists and then generate the plot
      if (!is.null(utility())) {
        plotdata <- utility()$out$data.sum.long
        EPs <- utility()$out$EPs
        wEPs <- utility()$wEPs
        mEPs <- utility()$mEPs
        title <- input$plottitle
        
        # Plot generation function - ensure this can save plots
        plot <- gen.plot(plotdata = plotdata, EPs = EPs, wEPs = wEPs, mEPs = mEPs, title = title)
        if (!is.null(utilityboot())) {
          pboot <- utilityboot()$pboot
          CI <- sapply(pboot, quantile, probs = c(0.025, 0.975))
          plot <- gen.plot.ci(plotdata = plotdata, CI = CI, EPs = EPs, wEPs = wEPs, mEPs = mEPs, title = title)
        }
        
        # Save the plot to a file
        png(file, width = 700, height = 500)
        print(plot)
        dev.off()
      }
    }
  )
  
  output$downloadCUI <- renderUI({
    if(!is.null(utility())){
      downloadButton('downloadsum', 'Download Utility Summary Table')
    }  
  })
  
  # combine input and output for download
  output$downloadsum <- downloadHandler(
    filename = function() {
      paste('CUIMET_input_output_summary', '.csv', sep='')
    },
    content = function(file) {
      cui.sum <- NULL
      if(!is.null(indata())){
        # combine input and output
        EPs <- indata()$EPs
        cnames <- c("Endpoint", "Weight", "Method", "Monotonicity")
        cui.input <- matrix(NA, nrow = length(EPs), ncol = length(cnames))
        cui.input <- data.frame(cui.input)
        colnames(cui.input) <- cnames
        cui.input$Endpoint <- EPs
        cui.input$Weight <- utility()$wEPs
        cui.input$Method <- utility()$mEPs
        cui.input$Monotonicity <- ifelse(EPs %in% c("Toxicity", utility()$EPs.mono), "Yes", "No")
        
        cui.output <- utility()$out$data.sum
        #cui.output$UtilityMean <- sprintf(cui.output$UtilityMean, fmt = fmt)
        #cui.output$UtilityWeightedMean <- sprintf(cui.output$UtilityWeightedMean, fmt = fmt)
        cui.sum <- matrix("", nrow = nrow(cui.input) + nrow(cui.output) + 5,
                          ncol = max(ncol(cui.input), ncol(cui.output)))
        cui.sum <- data.frame(cui.sum)
        colnames(cui.sum) <- NULL
        cui.sum[1, 1] <- "Input"
        cui.sum[2, 1:ncol(cui.input)] <- colnames(cui.input)
        cui.sum[2 + 1:nrow(cui.input), 1:ncol(cui.input)] <- cui.input
        cui.sum[nrow(cui.input) + 4, 1] <- "Utility Summary"
        cui.sum[nrow(cui.input) + 5, ] <- colnames(cui.output)
        cui.sum[(nrow(cui.input) + 6):nrow(cui.sum), ] <- cui.output
        cui.download <- cui.sum
        
        # combine bootstrap summary with cui.sum if it is available
        if(!is.null(utilityboot())){
          cui.output.boot <- data.frame(utilityboot()$pboot.sum, check.names = F)
          cui.sum.more <- matrix("",nrow = nrow(cui.sum) + 3 + nrow(cui.output.boot),
                                 ncol = max(ncol(cui.sum), ncol(cui.output.boot)))
          cui.sum.more <- data.frame(cui.sum.more)
          colnames(cui.sum.more) <- NULL
          cui.sum.more[1:nrow(cui.sum), 1:ncol(cui.sum)] <- cui.sum
          cui.sum.more[nrow(cui.sum) + 2, 1] <- "Utility Summary from Bootstrapping"
          cui.sum.more[nrow(cui.sum) + 3, ] <- colnames(cui.output.boot)
          cui.sum.more[(nrow(cui.sum) + 4):nrow(cui.sum.more), ] <- cui.output.boot
          cui.download <- cui.sum.more
        }
      }
      
      write.csv(cui.download, file, row.names = F, quote = F)
    }
  )
  
  # embed user guide
  output$help<-renderUI({
    tags$iframe(style = "height: 750px; width:100%; scrolling=yes", src = "CUIMET_UserGuide.pdf")
  })
  
}

# Run the application 
shinyApp(ui = ui, server = server)
