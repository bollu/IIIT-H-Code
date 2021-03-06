class AdminController < ApplicationController
  before_action  :kick_out_unauthorized?


  # === SURVEY STUFF ===
  def delete_survey
  if kick_out_unauthorized? then
      return
    end

    if not request.delete? then
        return
    end

    @survey = Survey.find_by({:name => survey_params[:name]})

    if @survey.nil? then
      flash[:error] = "Unable to find survey: " + survey_params[:name]
    else
      
    SurveyResponse.where({survey_id: @survey.id}).each do |resp|
      Answer.delete_all({survey_response_id: resp.id})
      resp.destroy
    end

      @survey.destroy
      redirect_to :controller => 'admin', :action => 'mainpage'
    end

  end
  
  def survey_add_question
    if kick_out_unauthorized? then
      return
    end

    if not request.post? then
        return
    end

    # take the current survey as @survey
    @survey  = Survey.find_by(name: question_params[:survey_name])
    
    if @survey.nil? then
      flash[:error] = "Unable to find survey: " + question_params[:survey_name]
      redirect_to :controller => 'admin', :action => 'mainpage'
      return
    end

    @question = @survey.questions.create(question_params)
    if @question.save then
        flash[:message] = "Successfully added question to Survey " + question_params[:survey_name]
        redirect_to :controller => 'admin', :action => 'mainpage'
    else
      flash[:error] = @survey.errors.full_messages
      redirect_to :controller => 'admin', :action => 'mainpage'
    end
  end


  def new_survey
  
    if kick_out_unauthorized? then
      return
    end

    if not request.post? then
        return
    end

    @survey = Survey.new(survey_params)

    if @survey.save
      flash[:message] = "successfully created Survey: " + @survey.name
      redirect_to :controller => 'admin', :action => 'mainpage'
    else
        flash[:error] = @survey.errors
        redirect_to :controller => 'admin', :action => 'new_survey'
    end
  end

  # === ADMIN STUFF ===

  # use this to kick out unauthorized profiles
  def kick_out_unauthorized?
    @unauthorized_allowed_actions = ['signup', 'login']
    
    if @unauthorized_allowed_actions.include?(params[:action]) then
      return
    end


    if not session.has_key?("admin_id") then
      redirect_to :controller => 'admin', :action => 'login'
    end
  end

  # Use this to automatically redirect to an authorized page
  def auto_redirect_to_mainpage?
    if session.has_key?("admin_id") then
      redirect_to_action = "mainpage"
      if params.has_key?(:redirect_to) then
        redirect_to_action = params[:redirect_to]
      end
      redirect_to :controller => 'admin', :action => redirect_to_action
    end

  end
  

  def logout
    session[:admin_id] = nil
    redirect_to :controller => 'admin', :action => 'login'
  end

  
  def login
    if auto_redirect_to_mainpage? then
      return
    end

   if not request.post? then
        return
    end

    @admin = Admin.find_by(username: admin_params[:username])

    if @admin.nil? then
      flash[:error] = {"username": ['does not exist']}
      redirect_to :controller => 'admin', :action => 'login'
    
    elsif !@admin.authenticate(admin_params[:password]) then
      flash[:error] = {"password": ["maybe incorrect"], "username": ["maybe incorrect"]}
      redirect_to :controller => 'admin', :action => 'login'
    else
      session["admin_id"] = @admin.id

      # TODO: allow custom redirects here
      redirect_to :controller => 'admin', :action => 'mainpage'
    end
  end




  def admin_params
    # HACK: this should be :admin?
    params.require(:user).permit(:username, :password)
  end

  def survey_params
    params.require(:survey).permit(:name)
  end

  def question_params
    params.require(:question).permit(:question, :survey_name)
  end

  def user_params
    params.require(:user).permit(:name, :email, :username, :password, :password_conformation)
  end


  # === USER STUFF ===
  def delete_user
   if not request.delete? then
        return
    end
    
    @user = User.find_by(username: user_params[:username])

    SurveyResponse.where({user_id: @user.id}).each do |resp|
      Answer.delete_all({survey_response_id: resp.id})
      resp.destroy
    end
    
    
    if not @user.nil? then
      puts "DELETING USER"
      @user.destroy
      redirect_to :controller => 'admin', :action => 'mainpage'
    end
  end

end
